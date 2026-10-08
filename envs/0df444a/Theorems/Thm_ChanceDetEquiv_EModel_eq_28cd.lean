-- Prove2me | Theorems.Thm_ChanceDetEquiv_EModel_eq_28cd
-- name    : ChanceDetEquiv.EModel.eq_28cd
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:56:45.016261+00:00
-- url     : https://prove2.me/theorems/1294976d-e293-444d-ab29-1905bf6fd541
-- title:
--   Eqs. (28c)–(28d) — for v_i ≥ 0, (28b) is equivalent to the squared pair −a_i′Dμ_b − v_i ≥ −μ_{b_i}, −K²E[b̂_i − a_i′Db̂]² + v_i² ≥ 0
-- statement:
--   Fix a row $i$ and a decision rule $D$, assume every $b_k$ is square integrable, and let $\tfrac12<\alpha_i<1$ and $v_i\ge0$. Then
--   $$\mu_{b_i}-a_i'D\mu_b\ge v_i\ \text{ and }\ v_i\ge K_{\alpha_i}\sqrt{E[\hat b_i-a_i'D\hat b]^2}$$
--   holds if and only if
--   $$-a_i'D\mu_b-v_i\ge-\mu_{b_i}\quad(28\text{c})\qquad\text{and}\qquad -K_{\alpha_i}^2E[\hat b_i-a_i'D\hat b]^2+v_i^2\ge0\quad(28\text{d}).$$
--
--   Squaring the nonnegative risk inequality removes the square root and produces a quadratic constraint in $(D,v_i)$; together with (28c) and $v_i\ge0$ this is the paper's form of each chance constraint before the substitution (30).
--
--   **Formalization Note** Normality is not needed for this algebraic equivalence. Square integrability ensures the displayed moment is an actual second moment, rather than the integral's junk value for a non-integrable function.
-- source:
--   Charnes and Cooper, Deterministic Equivalents for Optimizing and Satisficing under Chance Constraints, Oper. Res. 11 (1963), p. 28, Eqs. (28c)–(28d)

import Mathlib
import Definitions.Def_ChanceDetEquiv_EModel_Model

open MeasureTheory ProbabilityTheory Matrix

namespace ChanceDetEquiv.EModel

/-- **Eqs. (28c)–(28d)**, p. 28: for `½ < α_i < 1` and `v_i ≥ 0`, the pair (28b)
`μ_{b_i} − a_i'Dμ_b ≥ v_i ≥ K_{α_i} √E[b̂_i − a_i'Db̂]²` holds iff the squared pair
`−a_i'Dμ_b − v_i ≥ −μ_{b_i}` (28c) and `−K²_{α_i} E[b̂_i − a_i'Db̂]² + v_i² ≥ 0` (28d) holds. -/
theorem eq_28cd {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Ω → Fin m → ℝ)
    (hb : ∀ k, MemLp (fun ω => b ω k) 2 P)
    (D : Matrix (Fin n) (Fin m) ℝ) (i : Fin m)
    (α : ℝ) (hα_lo : 1 / 2 < α) (hα_hi : α < 1) (v : ℝ) (hv : 0 ≤ v) :
    (v ≤ meanVec P b i - (A *ᵥ (D *ᵥ meanVec P b)) i ∧
        K α * Real.sqrt (centeredSecondMoment P A b D i) ≤ v) ↔
      (-meanVec P b i ≤ -(A *ᵥ (D *ᵥ meanVec P b)) i - v ∧
        0 ≤ -(K α) ^ 2 * centeredSecondMoment P A b D i + v ^ 2) := by sorry

end ChanceDetEquiv.EModel
