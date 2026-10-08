-- Prove2me | Theorems.Thm_CorreaThreshold_Nonadaptive_cond_exp_tail_ge
-- name    : CorreaThreshold.Nonadaptive.cond_exp_tail_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:06.637275+00:00
-- url     : https://prove2.me/theorems/4e27a1c3-2d50-4e65-817c-24027eeda52b
-- title:
--   Proof of Theorem 1, p. 1460 — upper-tail stochastic dominance
-- statement:
--   Let the $X_i$ be independent, nonnegative random variables with continuous distributions. Fix an index $i$, and let $A_i$ be the event that $X_i$ is at least every other observation. Suppose a threshold $\alpha$ makes the upper-tail event $\{X_i>\alpha\}$ have the same probability as $A_i$. Then
--
--   $$\mathbb E[X_i\mathbf1_{A_i}]\le\mathbb E[X_i\mathbf1_{\{X_i>\alpha\}}].$$
--
--   This is the unnormalized form of the paper's conditional-expectation comparison, including the zero-probability case.
--
--   **Formalization Note** Independence and atomlessness carry the proof's standing assumptions. The expectations are nonnegative extended integrals, so an infinite value is retained.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1460, proof of Theorem 1, stochastic-dominance step; https://doi.org/10.1287/moor.2020.1105

import Mathlib
import Definitions.Def_CorreaThreshold_Nonadaptive_Setting

namespace CorreaThreshold.Nonadaptive

open MeasureTheory ProbabilityTheory

/-- An upper tail maximizes the expected prize among events of equal probability. -/
theorem cond_exp_tail_ge {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} [NeZero n]
    (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hXnn : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω)
    (hind : iIndepFun X P)
    (hcont : ∀ i, ∀ x : ℝ, P {ω | X i ω = x} = 0)
    (i : Fin n) (α : ℝ)
    (hα : P {ω | α < X i ω} = P {ω | ∀ j, X j ω ≤ X i ω}) :
    (∫⁻ ω, (if ∀ j, X j ω ≤ X i ω then
      ENNReal.ofReal (X i ω) else 0) ∂P) ≤
    (∫⁻ ω, (if α < X i ω then ENNReal.ofReal (X i ω) else 0) ∂P) := by sorry

end CorreaThreshold.Nonadaptive
