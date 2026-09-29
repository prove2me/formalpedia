-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart
-- name    : AlgebraicGeometry.Scheme.Opens.isAffineOpen_and_finite_aeval_of_twoChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/912ec6af-6925-5587-b510-a849fa108f19
-- title:
--   Complement of a pole: affineness and finiteness over R[f]
-- statement:
--   Let $R$ be a Noetherian commutative ring, $C$ a scheme and $c \colon C \to \operatorname{Spec} R$ a morphism that is proper, smooth of relative dimension $1$ and geometrically integral. Let $U, V$ be open subschemes of $C$ and let $f \in \Gamma(C, U)$, $g \in \Gamma(C, V)$. Assume $U \sqcup V = \top$, that $U \sqcap V$ is the basic open subset $\{g \neq 0\}$ of $V$, and that the restrictions of $f$ and of $g$ to $U \sqcap V$ satisfy $f|_{U \sqcap V} \cdot g|_{U \sqcap V} = 1$. Assume further that for every field $K$ equipped with an $R$-algebra structure the pull-back of $f$ along the first projection $\operatorname{pr}_1 \colon C \times_{\operatorname{Spec} R} \operatorname{Spec} K \to C$, viewed as a section over $\operatorname{pr}_1^{-1}(U)$, is transcendental over $K$ for the $K$-algebra structure on those sections induced by the second projection (the composite of the inverse of the canonical isomorphism $K \cong \Gamma(\operatorname{Spec} K, \top)$ with the restriction map of the second projection from the whole space to $\operatorname{pr}_1^{-1}(U)$). The conclusion is twofold: $U$ is an affine open of $C$, and, for the $R$-algebra structure on $\Gamma(C, U)$ obtained in the same way from $c$, the ring homomorphism $R[X] \to \Gamma(C, U)$ sending $X$ to $f$ is finite, i.e. $\Gamma(C, U)$ is a finitely generated module over the image of $R[X]$.
--
--   This is the 'complement of the pole divisor is affine, and finite over the affine line' half of the construction of a finite morphism from a relative smooth proper curve to $\mathbb{P}^1_R$ out of a section with a single pole; note that affineness of $U$ is part of the conclusion rather than a hypothesis. It is used in the construction of finite map data attached to a two-chart cover of such a curve, in particular by [`AlgebraicGeometry.SmoothProperCurve.exists_finiteMapData_le_isUnit_of_twoAffineOpenCover`](thm.html#AlgebraicGeometry.SmoothProperCurve.exists_finiteMapData_le_isUnit_of_twoAffineOpenCover), [`AlgebraicGeometry.SmoothProperCurve.exists_finiteMapData_m_eq_of_forall_invertible_free`](thm.html#AlgebraicGeometry.SmoothProperCurve.exists_finiteMapData_m_eq_of_forall_invertible_free) and [`AlgebraicGeometry.SmoothProperCurve.exists_twoAffineOpenCover_of_section`](thm.html#AlgebraicGeometry.SmoothProperCurve.exists_twoAffineOpenCover_of_section).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

theorem AlgebraicGeometry.Scheme.Opens.isAffineOpen_and_finite_aeval_of_twoChart
    {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (U V : C.Opens) (f : Γ(C, U)) (g : Γ(C, V))
    (hcov : U ⊔ V = ⊤) (hUV : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (hft : ∀ (K : Type u) [Field K] [Algebra R K],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
        ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)) ⁻¹ᵁ U);
      Transcendental K (((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)).app U).hom f)) :
    IsAffineOpen U ∧
      (letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
       (Polynomial.aeval f : R[X] →ₐ[R] Γ(C, U)).toRingHom.Finite) := by sorry
