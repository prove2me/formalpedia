-- Prove2me | Theorems.Thm_AlgebraicGeometry_isFinite_pullback_and_finrank_sections_eq_mul
-- name    : AlgebraicGeometry.isFinite_pullback_and_finrank_sections_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/d0f62117-0e0d-5cbe-a9ba-cf480624994d
-- title:
--   Finiteness and multiplicativity of sections for fibre products over a field
-- statement:
--   Let $\kappa$ be a field (in universe $u$), let $Y$ and $Z$ be schemes, and let $q_Y \colon Y \to \operatorname{Spec}\kappa$ and $q_Z \colon Z \to \operatorname{Spec}\kappa$ be morphisms of schemes, both assumed finite (`IsFinite`). The assertion has two parts. First, the composite of the first projection $\operatorname{pullback} q_Y\, q_Z \to Y$ with $q_Y$ is again a finite morphism. Second, equip the relevant rings of global sections with the $\kappa$-algebra structures supplied by `Scheme.TwoAffineOpenCover.algebraOfHom`: for a morphism $c \colon X \to \operatorname{Spec}(\kappa)$ and an open $U \subseteq X$ this is the algebra structure on $\Gamma(X, U)$ whose structure map is the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism for $\kappa$ followed by $c.\mathrm{appLE}\ \top\ U$, i.e. the map induced by $c$ on sections, restricted to $U$; it is applied here to the composite $\operatorname{pullback} q_Y\,q_Z \to Y \to \operatorname{Spec}\kappa$, to $q_Y$ and to $q_Z$, in each case with $U = \top$. With these structures, $$\dim_\kappa \Gamma(\operatorname{pullback} q_Y\, q_Z, \top) = \dim_\kappa \Gamma(Y, \top)\cdot \dim_\kappa \Gamma(Z, \top),$$ as an identity of `Module.finrank`s over $\kappa$.
--
--   This is the Künneth-type statement that the fibre product of two finite $\kappa$-schemes is finite and that its algebra of global sections has $\kappa$-dimension the product of the two dimensions, reflecting $\Gamma(Y \times_\kappa Z) \cong \Gamma(Y) \otimes_\kappa \Gamma(Z)$. It is used in the analysis of kernel structures on Néron models over a residue field, where it yields the finiteness and the rank formula for the relevant schemes of kernel points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isFinite_pullback_and_finrank_sections_eq_mul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isFinite_pullback_and_finrank_sections_eq_mul
    {κ : Type u} [Field κ] {Y Z : Scheme.{u}}
    (qY : Y ⟶ Spec (.of κ)) (qZ : Z ⟶ Spec (.of κ)) [IsFinite qY] [IsFinite qZ] :
    IsFinite (pullback.fst qY qZ ≫ qY) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst qY qZ ≫ qY) ⊤
     letI := Scheme.TwoAffineOpenCover.algebraOfHom qY ⊤
     letI := Scheme.TwoAffineOpenCover.algebraOfHom qZ ⊤
     Module.finrank κ Γ(pullback qY qZ, ⊤) = Module.finrank κ Γ(Y, ⊤) * Module.finrank κ Γ(Z, ⊤)) := by sorry
