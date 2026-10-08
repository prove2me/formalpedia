-- Prove2me | Theorems.Thm_ChanceDetEquiv_EModel_eq_25_27
-- name    : ChanceDetEquiv.EModel.eq_25_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:57:10.811519+00:00
-- url     : https://prove2.me/theorems/c2658902-891a-4f75-aba2-b2933062a13d
-- title:
--   Eqs. (22)–(27) — under normality and positive variance, P(a_i′Db ≤ b_i) ≥ α_i iff (−μ_{b_i} + a_i′Dμ_b)/√E[b̂_i − a_i′Db̂]² ≤ −K_{α_i}
-- statement:
--   Fix a row $i$ and a decision rule $D$. Assume every $b_k$ is square integrable, the variate $a_i'Db-b_i$ is normally distributed, and its variance is positive,
--   $$E[\hat b_i-a_i'D\hat b]^2>0,\qquad \hat b=b-\mu_b .$$
--   Let $\tfrac12<\alpha_i<1$ and $K_{\alpha_i}=\Phi^{-1}(\alpha_i)$. Then
--   $$P(a_i'Db\le b_i)\ge\alpha_i\iff\frac{-\mu_{b_i}+a_i'D\mu_b}{\sqrt{E[\hat b_i-a_i'D\hat b]^2}}\le-K_{\alpha_i}.$$
--
--   This is the passage (22)–(27) of the paper: the $i$-th chance constraint becomes a deterministic inequality in $D$ involving only the first two moments of $b$.
--
--   **Formalization Note** The paper writes $F_i^{-1}(\alpha_i)\equiv-K_{\alpha_i}$ with $F_i$ "the cumulant" of the standardised variate $z_i$; the step from (25) to (27) holds when $F_i$ is the upper-tail function $t\mapsto P(z_i\ge t)$, and then $K_{\alpha_i}=\Phi^{-1}(\alpha_i)>0$. The positive-variance hypothesis is the paper's ("made only to simplify the development", footnote † p. 27). $\alpha_i<1$ is added so that $K_{\alpha_i}$ is finite.
-- source:
--   Charnes and Cooper, Deterministic Equivalents for Optimizing and Satisficing under Chance Constraints, Oper. Res. 11 (1963), p. 27, Eqs. (22)–(27)

import Mathlib
import Definitions.Def_ChanceDetEquiv_EModel_Model

open MeasureTheory ProbabilityTheory Matrix

namespace ChanceDetEquiv.EModel

/-- **Eqs. (22)–(27)**, p. 27: for one row `i` and one decision rule `D`, if the variate
`a_i'Db − b_i` is normal, `E[b̂_i − a_i'Db̂]² > 0` and `½ < α_i < 1`, then the `i`-th chance
constraint `P(a_i'Db ≤ b_i) ≥ α_i` holds iff
`(−μ_{b_i} + a_i'Dμ_b) / √E[b̂_i − a_i'Db̂]² ≤ −K_{α_i}`. -/
theorem eq_25_27 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Ω → Fin m → ℝ)
    (hb : ∀ k, MemLp (fun ω => b ω k) 2 P)
    (D : Matrix (Fin n) (Fin m) ℝ) (i : Fin m)
    (hnormal : ∃ (μ : ℝ) (s : NNReal),
      P.map (fun ω => (A *ᵥ (D *ᵥ b ω)) i - b ω i) = gaussianReal μ s)
    (hvar : 0 < centeredSecondMoment P A b D i)
    (α : ℝ) (hα_lo : 1 / 2 < α) (hα_hi : α < 1) :
    α ≤ P.real {ω | (A *ᵥ (D *ᵥ b ω)) i ≤ b ω i} ↔
      (-meanVec P b i + (A *ᵥ (D *ᵥ meanVec P b)) i) / Real.sqrt (centeredSecondMoment P A b D i)
        ≤ -K α := by sorry

end ChanceDetEquiv.EModel
