-- Prove2me | Theorems.Thm_AvramDividend_Classical_three_mgf_limits_force_uniform_negative_tail_ws01f
-- name    : AvramDividend.Classical.three_mgf_limits_force_uniform_negative_tail_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:46:19.961989+00:00
-- url     : https://prove2.me/theorems/75315fb3-ffd6-46c9-aeb2-d7ce2aa9c57d
-- title:
--   A strict three-exponential-moment limit gap forces uniformly positive negative-tail probabilities
-- statement:
--   Given measurable real observations on a probability space with integrable exponential moments at three positive scales, suppose the three exponential-moment-minus-one integrals converge to a,b,c with a strict gap a>r²b+c/r. Then the negative-sign probability is bounded below by a fixed strictly positive number for all sufficiently large indices. This is the substantive probability transfer bridging the Lévy exponent asymptotic and the measurable negative-slope limsup, without weak convergence or pathwise jump estimates.
-- source:
--   WS1F accepted deterministic three-scale exponential inequality and remotely Proved integrated probability bound f35356ad; elementary real atTop convergence and strict-open neighbourhood.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_three_mgf_negative_probability_integral_bound_ws01f

open MeasureTheory Filter
open scoped Topology
open AvramDividend.Classical

theorem AvramDividend.Classical.three_mgf_limits_force_uniform_negative_tail_ws01f
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (r : ℝ) (hr : 1 ≤ r)
    (hY : ∀ n, Measurable (Y n))
    (h1 : ∀ n, Integrable (fun ω => Real.exp (Y n ω)) μ)
    (hs : ∀ n, Integrable (fun ω => Real.exp (Y n ω / r)) μ)
    (h2 : ∀ n, Integrable (fun ω => Real.exp (2 * Y n ω)) μ)
    (a b c : ℝ)
    (ha : Tendsto (fun n : ℕ =>
      ∫ ω, (Real.exp (Y n ω) - 1) ∂μ) atTop (nhds a))
    (hb : Tendsto (fun n : ℕ =>
      ∫ ω, (Real.exp (Y n ω / r) - 1) ∂μ) atTop (nhds b))
    (hc : Tendsto (fun n : ℕ =>
      ∫ ω, (Real.exp (2 * Y n ω) - 1) ∂μ) atTop (nhds c))
    (hgap : r ^ 2 * b + c / r < a) :
    ∃ p : ℝ, 0 < p ∧
      ∃ N : ℕ, ∀ n ≥ N,
        p ≤ μ.real {ω | Y n ω < 0} := by sorry
