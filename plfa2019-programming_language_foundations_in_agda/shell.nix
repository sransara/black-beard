with import <nixpkgs> {};

pkgs.mkShell {
  buildInputs = [
    (haskellPackages.ghcWithPackages (pkgs: [ 
      pkgs.Agda
    ]))
  ];
  shellHook = ''
cat << EOF > .agda-lib
name: resistance-is-futile
include: .
  ${pkgs.AgdaStdlib}/share/agda/
EOF
  '';
}
