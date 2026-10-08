-- Prove2me | Theorems.Thm_CvitanicKaratzas92_Existence_theorem_12_4
-- name    : CvitanicKaratzas92.Existence.theorem_12_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:25.867111+00:00
-- url     : https://prove2.me/theorems/f638514a-21f3-4061-b1cf-c1a05540a0af
-- title:
--   Theorem 12.4 — an optimal constrained policy exists under dual attainment
-- statement:
--   Under the assumptions of Proposition 12.2, including dual attainment (12.9), every initial capital $x>0$ has a constrained admissible portfolio–consumption policy $(\widehat\pi,\widehat c)$ with wealth process $\widehat X$ such that
--
--   $$J(\pi,c,X)\leq J(\widehat\pi,\widehat c,\widehat X)\quad\text{for every }(\pi,c,X)\in\mathcal A'(x).$$
--
--   This is the conditional existence theorem: Section 13 supplies the missing dual-attainment hypothesis.
--
--   **Formalization Note** The wealth process is bundled with the policy. Optimality is precisely (10.1); the extra marginal-integrability condition (10.2) is not imposed.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), p. 794, Theorem 12.4; https://doi.org/10.1214/aoap/1177005576

import Definitions.Def_CvitanicKaratzas92_Existence_Dual

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Existence

/-- Cvitanić–Karatzas (1992), Theorem 12.4, p. 794. -/
theorem theorem_12_4 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : VProc d Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (T : ℝ≥0) (M : Market d Ω) (I : ItoOperator d Ω)
    (K : Set (Vec d)) (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (h : Standing P W 𝓕 T M I K U1 U2)
    (h122 : Cond122 P 𝓕 T M I K U1 U2)
    (h123 : Cond123 T U1 U2)
    (h129 : Cond129 P 𝓕 T M I K U1 U2)
    (h825 : CvitanicKaratzas92.Optimality.Cond825 T U1 U2)
    (h1211 : Cond1211 U2) :
    ∀ x : ℝ, 0 < x → ∃ p : Policy d Ω,
      IsOptimal P 𝓕 T M I K U1 U2 x p := by sorry

end CvitanicKaratzas92.Existence
