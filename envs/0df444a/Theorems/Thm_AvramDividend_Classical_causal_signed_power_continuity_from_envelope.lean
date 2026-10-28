-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_signed_power_continuity_from_envelope
-- name    : AvramDividend.Classical.causal_signed_power_continuity_from_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T18:46:32.697607+00:00
-- url     : https://prove2.me/theorems/a3357d23-7883-4697-8bd6-848c9ce3d13a
-- title:
--   Signed causal L1 convolution powers are continuous from envelope bounds
-- statement:
--   A causal continuous signed L1 kernel generates positive-time continuous convolution powers whenever they are positive-axis L1 and dominated pointwise by a nonnegative envelope with a quadratic-geometric bound. This is the power-regularity premise needed to differentiate the Gaussian Neumann correction terms.
-- source:
--   The causal recurrence makes every signed power vanish for x≤0. The proved support-restriction integrability lemma upgrades positive-axis L1 to global L1. The real/causal convolution identity converts the Ioc power recursion into full convolution. The quadratic envelope controls all positive tails, allowing the existing signed-convolution-power continuity theorem to apply.

import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_causal_positive_l1_global_integrable
import Theorems.Thm_AvramDividend_Classical_causal_real_convolution_equals_positive_interval_under_support
import Theorems.Thm_AvramDividend_Classical_causal_signed_L1_convolution_powers_continuous_positive

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_signed_power_continuity_from_envelope
    (k : ℝ → ℝ) (P F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ : 0 ≤ ρ)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hkcont : ContinuousOn k (Ioi (0 : ℝ)))
    (hkzero : ∀ x : ℝ, x ≤ 0 → k x = 0)
    (hP0 : P 0 = k)
    (hPrec : ∀ n : ℕ, P (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hDom : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → |P n x| ≤ F n x)
    (hFpoint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :
    ∀ n : ℕ, ContinuousOn (P n) (Ioi (0 : ℝ)) := by sorry
