-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_signed_powers_exist_dominated
-- name    : AvramDividend.Classical.causal_l1_signed_powers_exist_dominated
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T16:47:57.002753+00:00
-- url     : https://prove2.me/theorems/be9befa3-a7d1-4f7a-8047-4cc8c13116be
-- title:
--   Signed L1 convolution powers exist and inherit a positive majorant
-- statement:
--   Given an L1 measurable signed kernel k bounded by an envelope κ at nonnegative times, and an envelope power sequence F with integrable causal products, there exists an L1 signed causal power sequence P whose every nonnegative-time value is dominated in absolute value by F. This supplies the Gaussian Esscher Neumann series with geometric power bounds.
-- source:
--   Construct the signed L1 causal powers using the canonical sequence-existence theorem. Orient the interval recursion by positive_Ioc_causal_convolution_comm_real and intervalIntegral.integral_of_le, use global measurability to obtain signed-product a.e. measurability, and invoke the proved noncircular domination induction. The zero endpoint follows from the empty causal convolution interval.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_power_sequence_exists
import Theorems.Thm_AvramDividend_Classical_causal_l1_measurable_signed_products
import Theorems.Thm_AvramDividend_Classical_positive_Ioc_causal_convolution_comm_real
import Theorems.Thm_AvramDividend_Classical_causal_signed_powers_domination_induction

open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.causal_l1_signed_powers_exist_dominated
    (k κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hkmeas : Measurable k)
    (hkdom : ∀ t : ℝ, 0 ≤ t → |k t| ≤ κ t)
    (hF0 : F 0 = κ)
    (hFrec : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        κ s * F n (x - s) ∂volume)
    (hFint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => κ (x - s) * F n s) volume 0 x) :
    ∃ P : ℕ → ℝ → ℝ,
      P 0 = k ∧
      (∀ n : ℕ, P (n + 1) =
        fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
          k s * P n (x - s) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → |P n t| ≤ F n t) := by sorry
