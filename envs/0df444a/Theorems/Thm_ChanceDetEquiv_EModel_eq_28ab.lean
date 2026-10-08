-- Prove2me | Theorems.Thm_ChanceDetEquiv_EModel_eq_28ab
-- name    : ChanceDetEquiv.EModel.eq_28ab
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:56:45.80257+00:00
-- url     : https://prove2.me/theorems/02d8d5cf-bff6-4e15-b191-dffd60968df9
-- title:
--   Eqs. (28a)–(28b) — (27) holds iff some v_i has μ_{b_i} − a_i′Dμ_b ≥ v_i ≥ K_{α_i}√E[b̂_i − a_i′Db̂]² ≥ 0
-- statement:
--   Fix a row $i$ and a decision rule $D$, assume every $b_k$ is square integrable and $E[\hat b_i-a_i'D\hat b]^2>0$, and let $\tfrac12<\alpha_i<1$. Then the inequality (27),
--   $$\frac{-\mu_{b_i}+a_i'D\mu_b}{\sqrt{E[\hat b_i-a_i'D\hat b]^2}}\le-K_{\alpha_i},$$
--   holds if and only if there is a real number $v_i$ with
--   $$\mu_{b_i}-a_i'D\mu_b\ \ge\ v_i\ \ge\ K_{\alpha_i}\sqrt{E[\hat b_i-a_i'D\hat b]^2}\ \ge\ 0 .$$
--
--   The new variable $v_i$ splits each constraint (27) into a "quality" part (the mean slack $\mu_i(D)$ dominates $v_i$) and a "risk" part ($v_i$ dominates $K_{\alpha_i}$ standard deviations).
--
--   **Formalization Note** The paper prints $a'_{b_i}$ in (28b); it is $a_i'$, as in (28a). The last inequality is a conclusion (it follows from $K_{\alpha_i}>0$), not a hypothesis.
-- source:
--   Charnes and Cooper, Deterministic Equivalents for Optimizing and Satisficing under Chance Constraints, Oper. Res. 11 (1963), p. 28, Eqs. (28a)–(28b)

import Mathlib
import Definitions.Def_ChanceDetEquiv_EModel_Model

open MeasureTheory ProbabilityTheory Matrix

namespace ChanceDetEquiv.EModel

/-- **Eqs. (28a)–(28b)**, p. 28: with `E[b̂_i − a_i'Db̂]² > 0` and `½ < α_i < 1`, the inequality (27)
holds iff there is a real `v_i` with
`μ_{b_i} − a_i'Dμ_b ≥ v_i ≥ K_{α_i} √E[b̂_i − a_i'Db̂]² ≥ 0`. -/
theorem eq_28ab {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Ω → Fin m → ℝ)
    (hb : ∀ k, MemLp (fun ω => b ω k) 2 P)
    (D : Matrix (Fin n) (Fin m) ℝ) (i : Fin m)
    (hvar : 0 < centeredSecondMoment P A b D i)
    (α : ℝ) (hα_lo : 1 / 2 < α) (hα_hi : α < 1) :
    (-meanVec P b i + (A *ᵥ (D *ᵥ meanVec P b)) i) / Real.sqrt (centeredSecondMoment P A b D i)
        ≤ -K α ↔
      ∃ v : ℝ, v ≤ meanVec P b i - (A *ᵥ (D *ᵥ meanVec P b)) i ∧
        K α * Real.sqrt (centeredSecondMoment P A b D i) ≤ v ∧
        0 ≤ K α * Real.sqrt (centeredSecondMoment P A b D i) := by sorry

end ChanceDetEquiv.EModel
