-- Prove2me | Theorems.Thm_AvramDividend_Classical_martingale_antitone_weight_supermartingale
-- name    : AvramDividend.Classical.martingale_antitone_weight_supermartingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:58:59.176977+00:00
-- url     : https://prove2.me/theorems/1b0ac8e1-4d2d-4d82-873f-6bff26d37b64
-- title:
--   Nonnegative martingale multiplied by a deterministic antitone weight is a supermartingale
-- statement:
--   If a real-valued martingale is almost surely nonnegative at every time, multiplying its value at time t by any deterministic nonincreasing real scalar c(t) produces a supermartingale. Strong adaptedness and integrability are inherited; the conditional expectation identity of the underlying martingale and positivity give the supermartingale inequality. This is the abstract bridge from a compensated exponential Lévy martingale to q-discounted exponential supermartingale tests.
-- source:
--   MeasureTheory.Martingale, MeasureTheory.Supermartingale, MeasureTheory.condExp_smul, and scalar monotonicity, pinned Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.martingale_antitone_weight_supermartingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (f : ℝ≥0 → Ω → ℝ) (hf : Martingale f 𝓕 μ)
    (hpos : ∀ t : ℝ≥0, ∀ᵐ ω ∂μ, 0 ≤ f t ω)
    (c : ℝ≥0 → ℝ) (hc : Antitone c) :
    Supermartingale (fun t ω => c t * f t ω) 𝓕 μ := by sorry
