-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_signed_powers_domination_induction
-- name    : AvramDividend.Classical.causal_signed_powers_domination_induction
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T16:19:09.60999+00:00
-- url     : https://prove2.me/theorems/c5a4cc44-6bfe-4bce-a32c-085327a3a033
-- title:
--   Inductive signed-power domination with integrability proved at each convolution step
-- statement:
--   For recursive signed and positive causal convolution powers, with signed kernels bounded by nonnegative envelopes, each signed convolution product measurable and each positive product interval-integrable, prove by induction that every signed power is pointwise dominated by its positive envelope on nonnegative time. At each stage signed-product integrability is derived from the inductive comparison, eliminating the circular hypothesis present in the direct power comparison theorem.
-- source:
--   Avoid the potential circularity between signed power domination and integrability: at stage n, domination of P_n by F_n and a measurable signed convolution integrand imply interval integrability by the positive-envelope product bridge. The Proved absolute convolution bound then propagates domination to n+1. The origin is handled by an explicit nonnegative-time boundary majorant.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_signed_integrable_product_of_envelope
import Theorems.Thm_AvramDividend_Classical_causal_signed_convolution_integral_abs_le_majorant

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_signed_powers_domination_induction
    (k κ : ℝ → ℝ) (P F : ℕ → ℝ → ℝ)
    (hkdom : ∀ t : ℝ, 0 ≤ t → |k t| ≤ κ t)
    (hP0 : P 0 = k) (hF0 : F 0 = κ)
    (hPsucc : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      P (n + 1) x =
        ∫ s in (0 : ℝ)..x, k (x - s) * P n s)
    (hFsucc : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F (n + 1) x =
        ∫ s in (0 : ℝ)..x, κ (x - s) * F n s)
    (hPzero : ∀ n : ℕ, |P n 0| ≤ F n 0)
    (hMeas : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      AEStronglyMeasurable
        (fun s : ℝ => k (x - s) * P n s)
        (volume.restrict (Ioc (0 : ℝ) x)))
    (hFint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      IntervalIntegrable
        (fun s : ℝ => κ (x - s) * F n s) volume 0 x) :
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → |P n t| ≤ F n t := by sorry
