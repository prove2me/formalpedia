-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_flat_of_comap_pullback_fst_eq
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.eq_of_flat_of_comap_pullback_fst_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/cf8e5a0d-90b1-5174-9496-8ab4ad5356ba
-- title:
--   Flat closed subschemes over a domain agreeing generically are equal
-- statement:
--   Let $R$ be a commutative ring which is an integral domain and let $K$ be a field equipped with an $R$-algebra structure making it a fraction field of $R$. Let $X$ be a scheme and $q : X \to \operatorname{Spec} R$ a morphism, and let $J_1, J_2$ be quasi-coherent ideal sheaf data on $X$ (elements of `X.IdealSheafData`), each with its associated closed subscheme and closed immersion `subschemeι` into $X$. Assume that for $i = 1, 2$ the composite of `Jᵢ.subschemeι` with $q$ is flat, i.e. the closed subscheme cut out by $J_i$ is flat over $\operatorname{Spec} R$. Write $p =$ `pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R K)))` for the first projection of the generic fibre $X_K = X \times_{\operatorname{Spec} R} \operatorname{Spec} K$ to $X$. The hypothesis is that the pullbacks (comaps) of the two ideal sheaves along $p$ coincide, $J_1.\mathrm{comap}\,p = J_2.\mathrm{comap}\,p$, as ideal sheaf data on $X_K$. The conclusion is $J_1 = J_2$.
--
--   This is the uniqueness half of the theory of schematic closure: a closed subscheme flat over a domain is determined by its generic fibre, so two flat closed subschemes of $X$ with the same restriction to $X_K$ agree. It is used in the Drinfeld-type descent step, where a divisor and a torsion subgroup scheme over a discrete valuation ring are recognised as flat closed subschemes of a projective model agreeing generically.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_flat_of_comap_pullback_fst_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.eq_of_flat_of_comap_pullback_fst_eq
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of R)) (J₁ J₂ : X.IdealSheafData)
    [Flat (J₁.subschemeι ≫ q)] [Flat (J₂.subschemeι ≫ q)]
    (h : J₁.comap (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R K)))) =
      J₂.comap (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    J₁ = J₂ := by sorry
