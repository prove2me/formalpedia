-- Prove2me | Theorems.Thm_CvitanicKaratzas92_Existence_proposition_12_2
-- name    : CvitanicKaratzas92.Existence.proposition_12_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:10.325975+00:00
-- url     : https://prove2.me/theorems/ca0b006b-7164-402a-a932-235fee75e8c4
-- title:
--   Proposition 12.2 — primal capital selects a minimizing dual parameter
-- statement:
--   Assume (12.2), the utility lower bounds (12.3), dual attainment (12.9), the common growth condition (8.25), and $U_2(\infty)=\infty$. For every choice $y\mapsto\lambda_y$ of the minimizers in (12.9) and every $x>0$, there is a $y(x)>0$ minimizing $\widetilde V(y)+xy$ over all $y>0$. It also satisfies
--
--   $$x=\mathcal X_{\lambda_{y(x)}}(y(x)).$$
--
--   This result matches the dual parameter to the prescribed initial capital, which is needed to turn Proposition 12.1 into an existence result for every $x$.
--
--   **Formalization Note** The choice function is explicit because $\mathcal X_{\lambda_y}$ depends on which minimizer is chosen. The budget map is an extended nonnegative real; equality with a positive real excludes an infinite budget value.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), p. 793, Proposition 12.2 and (12.11)–(12.12); https://doi.org/10.1214/aoap/1177005576

import Definitions.Def_CvitanicKaratzas92_Existence_Dual

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Existence

/-- Cvitanić–Karatzas (1992), Proposition 12.2, p. 793. -/
theorem proposition_12_2 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
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
    ∀ lam : ℝ → VProc d Ω,
      (∀ y : ℝ, 0 < y →
        IsD' P 𝓕 T M I K U1 U2 (lam y) ∧
        Vtilde P 𝓕 T M I K U1 U2 y = Jtilde P T M I K U1 U2 y (lam y)) →
      ∀ x : ℝ, 0 < x → ∃ y : ℝ, 0 < y ∧
        (∀ z : ℝ, 0 < z →
          Vtilde P 𝓕 T M I K U1 U2 y + ((x * y : ℝ) : EReal) ≤
            Vtilde P 𝓕 T M I K U1 U2 z + ((x * z : ℝ) : EReal)) ∧
        calX P T M I K U1 U2 (lam y) y = ENNReal.ofReal x := by sorry

end CvitanicKaratzas92.Existence
