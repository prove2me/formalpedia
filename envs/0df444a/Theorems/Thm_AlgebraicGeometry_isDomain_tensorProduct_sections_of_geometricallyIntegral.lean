-- Prove2me | Theorems.Thm_AlgebraicGeometry_isDomain_tensorProduct_sections_of_geometricallyIntegral
-- name    : AlgebraicGeometry.isDomain_tensorProduct_sections_of_geometricallyIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/77da8e50-16fb-5b44-a397-8d3063f6ae95
-- title:
--   Sections over an affine open stay a domain after base change to a field
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c \colon C \to \operatorname{Spec} R$ a morphism satisfying the predicate `GeometricallyIntegral`, the hypothesis from which integrality of the base changes of $c$ is obtained. Let $U$ be an open subscheme of $C$ with $U$ affine (hypothesis `hU`), and let $K$ be a field equipped with an $R$-algebra structure. Throughout, $\Gamma(C, U)$ carries the $R$-algebra structure `Scheme.TwoAffineOpenCover.algebraOfHom c U`, namely the one given by the ring map obtained from the morphism $(\mathrm{\Gamma Spec})^{-1}$ for $\mathrm{Spec}$ of $R$ followed by the component $c.\mathrm{appLE}\ \top\ U$ of $c$ on sections, i.e. by $R \to \Gamma(\operatorname{Spec} R, \top) \to \Gamma(C, U)$. Assume further that the $R$-module tensor product $K \otimes_R \Gamma(C, U)$ is nontrivial, i.e. not the zero ring. The conclusion is that $K \otimes_R \Gamma(C, U)$, with its ring structure as a tensor product of $R$-algebras, is an integral domain.
--
--   This is the ring-theoretic form of the statement that an affine chart of a scheme with geometrically integral fibres over $\operatorname{Spec} R$ remains integral after base change to a field, the nontriviality hypothesis excluding the case where the chart misses the relevant fibre. It is used in the analysis of two-chart affine covers of smooth proper curves, for instance in the computation of ranks of level sets and in étaleness criteria for them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isDomain_tensorProduct_sections_of_geometricallyIntegral.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isDomain_tensorProduct_sections_of_geometricallyIntegral
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [GeometricallyIntegral c] (U : C.Opens) (hU : IsAffineOpen U)
    (K : Type u) [Field K] [Algebra R K]
    (hne : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U; Nontrivial (K ⊗[R] Γ(C, U))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    IsDomain (K ⊗[R] Γ(C, U)) := by sorry
