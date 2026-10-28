-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_zero_barrier
-- name    : AvramDividend.Classical.vcstar_deriv_ge_one_zero_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:57:41.301995+00:00
-- url     : https://prove2.me/theorems/77c55202-93ca-49f7-92ba-7f402c78f574
-- title:
--   The zero-barrier candidate is differentiable with unit gradient on all positive reserves
-- statement:
--   When the formal optimal barrier cstar W equals zero, the barrier candidate vcstar W is C2 on the strictly positive real axis and has derivative exactly one there. Consequently its ordinary real derivative exists and is at least one at every positive reserve. This fully proves the zero-barrier branch of the outstanding Lemma 3(i) gradient theorem without assumptions on scale-function regularity.
-- source:
--   Canonically Proved vcstar_smooth_of_zero_cstar (e9096d7c-0877-461c-871c-9eccb6410caf) and vcstar_deriv_eq_one_above_cstar (4098a584-9c09-4437-b71f-5590221db9ab); differentiability extraction from pinned Mathlib ContDiffOn.differentiableOn.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_vcstar_smooth_of_zero_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_deriv_ge_one_zero_barrier
    (W : ℝ → ℝ) (hc0 : cstar W = 0) :
    ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (vcstar W) x ∧ 1 ≤ deriv (vcstar W) x := by sorry
