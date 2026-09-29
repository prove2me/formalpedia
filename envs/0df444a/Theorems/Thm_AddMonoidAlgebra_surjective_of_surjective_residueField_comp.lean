-- Prove2me | Theorems.Thm_AddMonoidAlgebra_surjective_of_surjective_residueField_comp
-- name    : AddMonoidAlgebra.surjective_of_surjective_residueField_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/ef99f139-6d4f-5032-ae59-abd2c67523e4
-- title:
--   Nakayama surjectivity for algebra maps to R[M]
-- statement:
--   Let $R$ be a commutative local ring with residue field $\kappa = \mathrm{ResidueField}\,R$, let $H$ be a commutative $R$-algebra, and let $M$ be a finite additive commutative monoid. Suppose given an $R$-algebra homomorphism $\psi \colon H \to R[M]$ into the additive monoid algebra of $M$ over $R$, together with a $\kappa$-algebra homomorphism $\psi_0 \colon \kappa \otimes_R H \to \kappa[M]$, assumed surjective as a function. The compatibility hypothesis is an equality of $R$-algebra homomorphisms $H \to \kappa[M]$: the composite of $\psi$ with the coefficientwise map $R[M] \to \kappa[M]$ induced by the canonical map $R \to \kappa$ (via `AddMonoidAlgebra.mapAlgHom` and `Algebra.ofId`) agrees with the composite of $h \mapsto 1 \otimes h$ (`Algebra.TensorProduct.includeRight`) followed by $\psi_0$ regarded as an $R$-algebra map by restriction of scalars. The conclusion is that $\psi$ itself is surjective. Note that $R$ and $H$ lie in the same universe, while $M$ may lie in another.
--
--   This is Nakayama's lemma in the form: an $R$-algebra map into the finite free $R$-module $R[M]$ whose reduction to the residue field is surjective is already surjective; equivalently, a morphism of finite $R$-schemes that is a closed immersion on the special fibre is a closed immersion. It is used in the construction of lifts of split tori (a unique lift of a closed immersion of finite multiplicative-type group schemes over a henselian local ring), in [`AlgebraicGeometry.SplitTorus.existsUnique_muLift_of_torusFibre_of_henselian`](thm.html#AlgebraicGeometry.SplitTorus.existsUnique_muLift_of_torusFibre_of_henselian).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddMonoidAlgebra_surjective_of_surjective_residueField_comp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IsLocalRing
open scoped TensorProduct

theorem AddMonoidAlgebra.surjective_of_surjective_residueField_comp
    {R : Type u} [CommRing R] [IsLocalRing R]
    {H : Type u} [CommRing H] [Algebra R H]
    (M : Type v) [AddCommMonoid M] [Finite M]
    (ψ : H →ₐ[R] AddMonoidAlgebra R M)
    (ψ₀ : ResidueField R ⊗[R] H →ₐ[ResidueField R] AddMonoidAlgebra (ResidueField R) M)
    (hψ₀ : Function.Surjective ψ₀)
    (hred : (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).comp ψ =
      (ψ₀.restrictScalars R).comp Algebra.TensorProduct.includeRight) :
    Function.Surjective ψ := by sorry
