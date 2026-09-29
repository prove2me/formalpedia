-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_restrictAlong_eq_of_finiteDimensional_fieldRange
-- name    : AlgebraicCurve.Place.exists_restrictAlong_eq_of_finiteDimensional_fieldRange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/c53c0e38-6d3b-5a6a-b8a3-b01da4e6473d
-- title:
--   Places extend along an integral map of function fields
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$, and let $\varphi : F \to F'$ be a $K$-algebra homomorphism whose underlying ring homomorphism is integral, so that $F'$ becomes an $F$-algebra via $\varphi$. Assume moreover that $F'$ is finite-dimensional over the subfield $\varphi.\mathrm{fieldRange} \subseteq F'$, the image of $\varphi$, and that $F'$ is separable over that image. Here a `Place` of $F$ over $K$ is a valuation subring $\mathcal{O} \subseteq F$ such that $\mathcal{O}$ contains the image of $K$ under $\mathrm{algebraMap}\,K\,F$, such that $\mathcal{O} \neq \top$, and such that $\mathcal{O}$ is a principal ideal ring; and the restriction `Place.restrictAlong` of a place $w$ of $F'$ over $K$ along $\varphi$ is the place of $F$ whose valuation subring is the preimage $\varphi^{-1}(\mathcal{O}_w)$. The conclusion is that for every place $v$ of $F$ over $K$ there exists a place $w$ of $F'$ over $K$ whose restriction along $\varphi$ equals $v$.
--
--   This is the lying-over (Chevalley extension) statement in the form used for covers of curves: every place of the base extends to the cover, here under the hypotheses that the cover is finite and separable over the image subfield. It is invoked in the analysis of charts, poles and nodes on modular curves over level fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_restrictAlong_eq_of_finiteDimensional_fieldRange.lean

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Place.exists_restrictAlong_eq_of_finiteDimensional_fieldRange
    {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    [FiniteDimensional φ.fieldRange F'] [Algebra.IsSeparable φ.fieldRange F']
    (v : AlgebraicCurve.Place K F) :
    ∃ w : AlgebraicCurve.Place K F', w.restrictAlong φ hφ = v := by sorry
