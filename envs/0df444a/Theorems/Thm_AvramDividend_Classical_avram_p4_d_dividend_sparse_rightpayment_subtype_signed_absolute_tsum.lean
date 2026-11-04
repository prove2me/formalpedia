-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_sparse_rightpayment_subtype_signed_absolute_tsum
-- name    : AvramDividend.Classical.avram_p4_d_dividend_sparse_rightpayment_subtype_signed_absolute_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:30:15.790727+00:00
-- url     : https://prove2.me/theorems/687b9654-7d4a-46f5-a1e1-dbb8809b54e3
-- title:
--   Sparse original right-dividend correction inherits signed and absolute convergent series from positive-payment carrier
-- statement:
--   The true original right-payment correction vanishes whenever the dividend right increment is zero. A generic real-series transport on the strictly positive right-payment carrier preserves Summable, nonpositive signed tsum, Summable absolute values and an exact absolute-cash bound. This small polymorphic lemma isolates the pinned Mathlib subtype and indicator summation equivalences to avoid repeated expensive definitional expansion of the original Lévy source and Stieltjes expressions.
-- source:
--   Pinned Mathlib summable_subtype_iff_indicator, tsum_subtype_eq_of_support_subset; original source P4-D accepted positive-atom budget 4471f6e4.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal Classical
noncomputable section

/-- A right-payment correction vanishing off its actual positive-atom carrier inherits the subtype signed and absolute budget. -/

theorem AvramDividend.Classical.avram_p4_d_dividend_sparse_rightpayment_subtype_signed_absolute_tsum
    {ι : Type*} (S : Set ι) (J : ι → ℝ) (B : ℝ)
    (hzero : ∀ i, i ∉ S → J i = 0)
    (hSummS : Summable (fun a : S => J a.val))
    (hNonposS : (∑' a : S, J a.val) ≤ 0)
    (hAbsS : Summable (fun a : S => |J a.val|))
    (hBoundS : (∑' a : S, |J a.val|) ≤ B) :
    Summable J ∧ (∑' i : ι, J i) ≤ 0 ∧
      Summable (fun i : ι => |J i|) ∧ (∑' i : ι, |J i|) ≤ B := by sorry
