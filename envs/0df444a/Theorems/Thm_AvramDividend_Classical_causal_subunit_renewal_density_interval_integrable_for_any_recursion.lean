-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_density_interval_integrable_for_any_recursion
-- name    : AvramDividend.Classical.causal_subunit_renewal_density_interval_integrable_for_any_recursion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:35:37.889413+00:00
-- url     : https://prove2.me/theorems/c4b1bc3a-360c-4628-a00f-56e1197d04f0
-- title:
--   Every uniquely defined subunit causal renewal convolution series is integrable from zero
-- statement:
--   For any real-valued convolution power sequence satisfying the same causal subunit positive renewal kernel recursion, the pointwise infinite density series is interval integrable from zero to every positive endpoint. Unique recursion identifies this arbitrary sequence with the canonical sequence in the already Proved causal_subunit_renewal_density_interval_integrable_at_zero. This is the exact universal-F integrability conjunct in the remaining scaled BV Esscher scale identification 1ca4a724, avoiding a fresh analytic proof for every candidate convolution sequence.
-- source:
--   Canonical causal_subunit_renewal_density_interval_integrable_at_zero and Nat recursion uniqueness.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_density_interval_integrable_at_zero
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_subunit_renewal_density_interval_integrable_for_any_recursion
    (κ : ℝ → ℝ) (ρ : ℝ)
    (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκpos : ∀ x : ℝ, 0 ≤ x → 0 ≤ κ x)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hmass : (∫ x in Ioi (0 : ℝ), κ x ∂volume) = ρ)
    (F : ℕ → ℝ → ℝ)
    (hFzero : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) :
    ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun y : ℝ => ∑' n : ℕ, F n y)
        volume 0 x := by sorry
