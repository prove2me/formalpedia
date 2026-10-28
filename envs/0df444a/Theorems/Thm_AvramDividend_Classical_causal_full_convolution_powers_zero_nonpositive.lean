-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_zero_nonpositive
-- name    : AvramDividend.Classical.causal_full_convolution_powers_zero_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:19:38.76904+00:00
-- url     : https://prove2.me/theorems/5af37937-78f0-4271-9507-3e56c9285042
-- title:
--   Recursive full-real causal convolution powers vanish at nonpositive times
-- statement:
--   If a base kernel is zero on nonpositive times, every member of a recursively defined full-real convolution-power sequence also vanishes there. The induction uses the already-Proved convolution support theorem. This supplies the causal support prerequisite for the positive-time renewal density's zero-endpoint integrability and Esscher kernel series constructions.

import Theorems.Thm_AvramDividend_Classical_causal_convolution_zero_nonpositive

open AvramDividend.Classical MeasureTheory

theorem AvramDividend.Classical.causal_full_convolution_powers_zero_nonpositive
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hFzero : F 0 = κ)
    (hFrec : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) :
    ∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → F n x = 0 := by sorry
