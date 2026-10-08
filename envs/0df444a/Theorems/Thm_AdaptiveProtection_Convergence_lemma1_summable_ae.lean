-- Prove2me | Theorems.Thm_AdaptiveProtection_Convergence_lemma1_summable_ae
-- name    : AdaptiveProtection.Convergence.lemma1_summable_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:37.535234+00:00
-- url     : https://prove2.me/theorems/e86cb4de-c423-4c73-958d-5a78d579ee79
-- title:
--   Lemma 1, p. 764 (Lukács 1975, Thm 4.2.1) — Σ_n E|Y_n| < ∞ implies Σ_n |Y_n| < ∞ a.s.
-- statement:
--   Let $(Y_n)_{n \ge 0}$ be a sequence of integrable real random variables on a probability space $(\Omega, \mathcal F, P)$ with
--   $$\sum_n E|Y_n| < +\infty.$$
--   Then
--   $$\sum_n |Y_n| < +\infty \quad \text{almost surely.}$$
--
--   In the proof of Theorem 1 this turns the summability in mean of $\gamma_n|\theta^n_i - \theta^*_i|$ into almost-sure summability.
--
--   **Formalization Note** The page's hypothesis "$EY_n < +\infty$ for all $n$" is read as integrability of each $Y_n$, which the summability of $E|Y_n|$ already forces.
-- source:
--   van Ryzin & McGill, Management Science 46(6), 2000, p. 764, Lemma 1 (citing Lukács 1975, Theorem 4.2.1)

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model
import Definitions.Def_AdaptiveProtection_Convergence_Setting

open MeasureTheory Filter Topology

namespace AdaptiveProtection.Convergence

/-- Lemma 1 (p. 764; Lukács 1975, Theorem 4.2.1): if `∑_n E|Y_n| < ∞`, then `∑_n |Y_n| < ∞` a.s. -/
theorem lemma1_summable_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Integrable (Y n) μ)
    (hsum : Summable fun n => ∫ ω, |Y n ω| ∂μ) :
    ∀ᵐ ω ∂μ, Summable fun n => |Y n ω| := by sorry

end AdaptiveProtection.Convergence
