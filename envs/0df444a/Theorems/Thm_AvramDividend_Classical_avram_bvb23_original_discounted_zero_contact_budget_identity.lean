-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_discounted_zero_contact_budget_identity
-- name    : AvramDividend.Classical.avram_bvb23_original_discounted_zero_contact_budget_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:20:49.459276+00:00
-- url     : https://prove2.me/theorems/5ce1f298-6a16-4098-8619-66afe89a53c7
-- title:
--   Exact finite-horizon discounted contact cash and terminal identity for original BV source zero-contact budget
-- statement:
--   The discount integral on every finite physical horizon satisfies the exact identity: the discounted running rate integral multiplied by q, plus the terminal discount, equals one. This is the precise scalar cancellation required to combine source-proved zero-contact physical drift/Stieltjes cash bounds with the original negative-mark compensation rate and the full-horizon terminal reward. No surrogate stochastic process or open-mask assumption is introduced.
-- source:
--   Pinned Mathlib intervalIntegral.integral_deriv_eq_sub prime fundamental theorem of calculus and real exponential derivative; Avram-Palmowski-Pistorius (2007), Eq. (5.13).

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb23_original_discounted_zero_contact_budget_identity
    (q T : ℝ) (hq : 0 < q) (hT : 0 ≤ T) :
    q * (∫ t in (0 : ℝ)..T, Real.exp ((-q) * t)) +
      Real.exp ((-q) * T) = 1 := by sorry
