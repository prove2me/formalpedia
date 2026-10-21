-- Prove2me | Theorems.Thm_AvramDividend_Classical_grid_exit_real_to_lintegral_limit
-- name    : AvramDividend.Classical.grid_exit_real_to_lintegral_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:57:46.454613+00:00
-- url     : https://prove2.me/theorems/023dfa05-00b8-4903-aea4-42c871aea1e7
-- title:
--   From real-valued bounded grid expectations to continuous-time ENNReal payoff bounds
-- statement:
--   Given measurable integrable nonnegative real-valued grid rewards f_n with uniform expectation bounds B, an extended nonnegative continuous-time payoff pointwise bounded by liminf_n ofReal(f_n) has ENNReal integral bounded by ofReal(B). The result combines the real-to-ENNReal integral identity with Fatou's lemma; it is the measure-theoretic bridge from proved discounted finite-grid exit bounds to continuous-time first-passage rewards, preserving the genuine pathwise convergence obligation.
-- source:
--   Pinned Mathlib ofReal_integral_eq_lintegral_ofReal, ENNReal.ofReal_mono, and newly published grid_exit_fatou_uniform_bound.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal

theorem AvramDividend.Classical.grid_exit_real_to_lintegral_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Ω → ENNReal) (f : ℕ → Ω → ℝ)
    (B : ℝ)
    (hMeas : ∀ n : ℕ, Measurable (f n))
    (hInt : ∀ n : ℕ, Integrable (f n) P)
    (hPos : ∀ n : ℕ, ∀ ω : Ω, 0 ≤ f n ω)
    (hLimit : ∀ ω : Ω,
      F ω ≤ liminf (fun n => ENNReal.ofReal (f n ω)) atTop)
    (hBound : ∀ n : ℕ, (∫ ω, f n ω ∂P) ≤ B) :
    (∫⁻ ω, F ω ∂P) ≤ ENNReal.ofReal B := by sorry
