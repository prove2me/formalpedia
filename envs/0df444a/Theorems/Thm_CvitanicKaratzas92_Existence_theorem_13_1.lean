-- Prove2me | Theorems.Thm_CvitanicKaratzas92_Existence_theorem_13_1
-- name    : CvitanicKaratzas92.Existence.theorem_13_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:55.027189+00:00
-- url     : https://prove2.me/theorems/36d90f50-3873-4ad4-8df4-2ac4b5c38d86
-- title:
--   Theorem 13.1 — dual attainment and existence of an optimal constrained policy
-- statement:
--   Let the Brownian market, its augmented filtration, the closed convex portfolio constraint $K$, and the running and terminal utilities satisfy the standing assumptions of Sections 2–8, including Assumption 6.2. Assume condition (5.8) for both utilities, one common pair of constants in (8.25), dual finiteness (12.2), the lower bounds (12.3), and $U_2(\infty)=\infty$ from (12.11). Then both conclusions of Theorem 13.1 hold:
--
--   $$\forall y>0\;\exists\lambda_y\in\mathcal D':\quad\widetilde V(y)=\widetilde J(y;\lambda_y),$$
--
--   and, for every $x>0$, there is a constrained admissible policy $(\widehat\pi,\widehat c,\widehat X)\in\mathcal A'(x)$ whose expected utility is at least that of every policy in $\mathcal A'(x)$.
--
--   The theorem establishes dual attainment and existence of an optimal constrained portfolio–consumption pair for each initial capital.
--
--   **Formalization Note** Condition (12.9) is the first conclusion, never a hypothesis. The wealth process is carried with the policy. The Itô operator is constrained by its local stochastic-integral relation, and extended-real expectations and support values preserve infinite cases. Optimality does not include (10.2).
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), p. 794, Theorem 13.1; https://doi.org/10.1214/aoap/1177005576

import Definitions.Def_CvitanicKaratzas92_Existence_Dual

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Existence

/-- Cvitanić–Karatzas (1992), Theorem 13.1, p. 794. -/
theorem theorem_13_1 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : VProc d Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (T : ℝ≥0) (M : Market d Ω) (I : ItoOperator d Ω)
    (K : Set (Vec d)) (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (h : Standing P W 𝓕 T M I K U1 U2)
    (h58 : Cond58 T U1 U2) (h825 : CvitanicKaratzas92.Optimality.Cond825 T U1 U2)
    (h122 : Cond122 P 𝓕 T M I K U1 U2)
    (h123 : Cond123 T U1 U2) (h1211 : Cond1211 U2) :
    Cond129 P 𝓕 T M I K U1 U2 ∧
      ∀ x : ℝ, 0 < x → ∃ p : Policy d Ω,
        IsOptimal P 𝓕 T M I K U1 U2 x p := by sorry

end CvitanicKaratzas92.Existence
