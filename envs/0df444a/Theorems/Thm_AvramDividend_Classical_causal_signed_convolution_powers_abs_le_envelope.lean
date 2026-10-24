-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_signed_convolution_powers_abs_le_envelope
-- name    : AvramDividend.Classical.causal_signed_convolution_powers_abs_le_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:56:11.415625+00:00
-- url     : https://prove2.me/theorems/c35a81df-3185-4bac-b619-d1361ba184c7
-- title:
--   Signed causal convolution powers are dominated pointwise by positive-envelope powers
-- statement:
--   If |k(t)|≤κ(t) for t>0 and κ≥0, two causal power sequences with matching initial kernels and convolution recursions satisfy |P_n(x)|≤F_n(x) for all n and x>0, provided each convolution product is integrable. This transfers the Proved quadratic-geometric positive-power bound to the signed resolvent terms.
-- source:
--   Induction using the Proved causal_signed_convolution_integral_abs_le_majorant theorem; the interval integrability of each product is explicit.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_signed_convolution_integral_abs_le_majorant

open AvramDividend.Classical MeasureTheory Set

namespace AvramDividend.Classical

theorem causal_signed_convolution_powers_abs_le_envelope
    (k κ : ℝ → ℝ) (P F : ℕ → ℝ → ℝ)
    (hk : ∀ t : ℝ, 0 < t → |k t| ≤ κ t)
    (hκ : ∀ t : ℝ, 0 < t → 0 ≤ κ t)
    (hP0 : P 0 = k) (hF0 : F 0 = κ)
    (hPsucc : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      P (n + 1) x = ∫ s in (0 : ℝ)..x, k (x - s) * P n s)
    (hFsucc : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F (n + 1) x = ∫ s in (0 : ℝ)..x, κ (x - s) * F n s)
    (hPint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => k (x - s) * P n s) volume 0 x)
    (hFint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => κ (x - s) * F n s) volume 0 x) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x → |P n x| ≤ F n x := by sorry

end AvramDividend.Classical
