-- Prove2me | Theorems.Thm_CvitanicKaratzas92_Existence_eq_12_8
-- name    : CvitanicKaratzas92.Existence.eq_12_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:04.982334+00:00
-- url     : https://prove2.me/theorems/1e2c038c-89e4-427b-927b-49c717bd5663
-- title:
--   (12.8) — weak duality for constrained and auxiliary markets
-- statement:
--   Let $V(x)$ be the maximal expected utility attainable with a portfolio constrained to $K$ and initial capital $x$, and let $\widetilde V(y)$ be the infimum of the auxiliary dual objective over $\mathcal D$. For every $x,y>0$,
--
--   $$V(x)\leq\widetilde V(y)+xy.$$
--
--   This weak-duality inequality bounds the constrained primal problem by every positive dual parameter and is used in the later dual representation.
--
--   **Formalization Note** The values are extended real, so an empty admissible class or an infinite dual value keeps its mathematical meaning. All market, constraint, utility, filtration, and Itô-integral assumptions of Sections 2–6 are carried by the shared standing predicate.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), p. 792, Section 12, (12.8); https://doi.org/10.1214/aoap/1177005576

import Definitions.Def_CvitanicKaratzas92_Existence_Dual

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Existence

/-- Cvitanić–Karatzas (1992), (12.8), p. 792. -/
theorem eq_12_8 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : VProc d Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (T : ℝ≥0) (M : Market d Ω) (I : ItoOperator d Ω)
    (K : Set (Vec d)) (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (h : Standing P W 𝓕 T M I K U1 U2) :
    ∀ x y : ℝ, 0 < x → 0 < y →
      V P 𝓕 T M I K U1 U2 x ≤
        Vtilde P 𝓕 T M I K U1 U2 y + ((x * y : ℝ) : EReal) := by sorry

end CvitanicKaratzas92.Existence
