-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_signed_L1_convolution_powers_continuous_positive
-- name    : AvramDividend.Classical.causal_signed_L1_convolution_powers_continuous_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:20:30.901348+00:00
-- url     : https://prove2.me/theorems/26a66321-a6de-4399-98f2-087cb4d9758b
-- title:
--   Positive-time continuity of signed causal L1 convolution powers
-- statement:
--   A causal L1 kernel continuous on positive times generates continuous signed convolution powers whenever each power remains L1, causal, and bounded on positive tails. This supplies regularity for signed damped Gaussian Volterra Neumann terms, which are controlled by the previously Proved positive-envelope powers.
-- source:
--   Induction from the Proved causal convolution continuity theorem, using signed tail bounds instead of positivity.

import Mathlib.Analysis.Convolution
import Theorems.Thm_AvramDividend_Classical_continuousOn_positive_causal_convolution_of_locally_bounded_integrable

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_signed_L1_convolution_powers_continuous_positive
    (k : ℝ → ℝ) (P : ℕ → ℝ → ℝ)
    (hkint : Integrable k volume)
    (hkcont : ContinuousOn k (Ioi (0 : ℝ)))
    (hkzero : ∀ x : ℝ, x ≤ 0 → k x = 0)
    (hkbound : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |k x| ≤ M)
    (hP0 : P 0 = k)
    (hPsucc : ∀ n : ℕ, P (n + 1) =
      fun x : ℝ => ∫ y : ℝ, k y * P n (x - y) ∂volume)
    (hPint : ∀ n : ℕ, Integrable (P n) volume)
    (hPzero : ∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → P n x = 0)
    (hPbound : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |P n x| ≤ M) :
    ∀ n : ℕ, ContinuousOn (P n) (Ioi (0 : ℝ)) := by sorry
