-- Prove2me | Theorems.Thm_Algebra_Etale_existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
-- name    : Algebra.Etale.existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/396d61dd-4f68-5863-9844-60093f095234
-- title:
--   Lifting algebra maps from a finite étale algebra over a henselian local ring
-- statement:
--   Let $R$ be a commutative ring which is a henselian local ring, and write $k = \mathrm{IsLocalRing.ResidueField}\ R$ for its residue field. Let $O$ be a commutative $R$-algebra which is finite as an $R$-module and étale over $R$, and let $C$ be a commutative $R$-algebra which is finite as an $R$-module (no étaleness is assumed of $C$). Let $\bar\psi \colon k \otimes_R O \to k \otimes_R C$ be a homomorphism of $k$-algebras between the two base changes to the residue field. The assertion is that there is exactly one homomorphism of $R$-algebras $\psi \colon O \to C$ whose base change along $R \to k$ is $\bar\psi$, that is, such that the map $k \otimes_R O \to k \otimes_R C$ obtained by tensoring the identity of $k$ with $\psi$ equals $\bar\psi$. Equivalently, reduction modulo the maximal ideal of $R$ is a bijection from $R$-algebra homomorphisms $O \to C$ onto $k$-algebra homomorphisms $k \otimes_R O \to k \otimes_R C$.
--
--   This is Hensel's lemma for homomorphisms out of a finite étale algebra over a henselian local ring: such homomorphisms into an arbitrary module-finite algebra are determined by, and lift uniquely from, their reductions to the residue field. The proof combines the corresponding rigidity statement (two $R$-algebra maps from a finite étale algebra agreeing modulo the maximal ideal coincide) with the decomposition of a module-finite algebra over a henselian local ring into local factors by complete orthogonal idempotents; it is used in the corresponding lifting statements for bialgebra homomorphisms and for Hopf algebras over henselian local rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_Etale_existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem Algebra.Etale.existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (O : Type v) [CommRing O] [Algebra R O] [Module.Finite R O] [Algebra.Etale R O]
    (C : Type w) [CommRing C] [Algebra R C] [Module.Finite R C]
    (ψbar : IsLocalRing.ResidueField R ⊗[R] O →ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R ⊗[R] C) :
    ∃! ψ : O →ₐ[R] C,
      Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)) ψ = ψbar := by sorry
