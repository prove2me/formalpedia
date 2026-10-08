-- Prove2me | Theorems.Thm_CvitanicKaratzas92_Existence_proposition_12_1
-- name    : CvitanicKaratzas92.Existence.proposition_12_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:19.604634+00:00
-- url     : https://prove2.me/theorems/c18320e8-58e4-4fec-a108-6d9991b99e1e
-- title:
--   Proposition 12.1 — a dual minimizer yields a primal optimum and conjugate representation
-- statement:
--   Assume (12.2) and (12.9). For every $y>0$ and every chosen minimizer $\lambda_y\in\mathcal D'$ of $\widetilde J(y;\cdot)$, put $x=\mathcal X_{\lambda_y}(y)$. Then $x>0$, and an admissible constrained policy with initial capital $x$ attains $V(x)$. Moreover,
--
--   $$\widetilde V(y)=\sup_{\xi>0}\{V(\xi)-y\xi\},\qquad y>0,$$
--
--   and $\widetilde V$ is convex on $(0,\infty)$. The result connects dual attainment to an actual optimal portfolio and identifies the dual value as a conjugate of the primal value.
--
--   **Formalization Note** A policy is represented with its wealth process. The chosen minimizer is universally quantified among the witnesses of (12.9). Convexity is stated with extended-real affine combinations, preserving possible infinite values.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), p. 792, Proposition 12.1 and (12.9)–(12.10); https://doi.org/10.1214/aoap/1177005576

import Definitions.Def_CvitanicKaratzas92_Existence_Dual

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Existence

/-- Cvitanić–Karatzas (1992), Proposition 12.1, p. 792. -/
theorem proposition_12_1 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : VProc d Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (T : ℝ≥0) (M : Market d Ω) (I : ItoOperator d Ω)
    (K : Set (Vec d)) (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (h : Standing P W 𝓕 T M I K U1 U2)
    (h122 : Cond122 P 𝓕 T M I K U1 U2)
    (h129 : Cond129 P 𝓕 T M I K U1 U2) :
    (∀ y : ℝ, 0 < y → ∀ lam : VProc d Ω,
      IsD' P 𝓕 T M I K U1 U2 lam →
      Vtilde P 𝓕 T M I K U1 U2 y = Jtilde P T M I K U1 U2 y lam →
      let x := (calX P T M I K U1 U2 lam y).toReal
      0 < x ∧ ∃ p : Policy d Ω, IsOptimal P 𝓕 T M I K U1 U2 x p) ∧
    (∀ y : ℝ, 0 < y →
      Vtilde P 𝓕 T M I K U1 U2 y =
        ⨆ ξ : {ξ : ℝ // 0 < ξ},
          V P 𝓕 T M I K U1 U2 ξ.val - ((y * ξ.val : ℝ) : EReal)) ∧
    EConvexOn (Vtilde P 𝓕 T M I K U1 U2) := by sorry

end CvitanicKaratzas92.Existence
