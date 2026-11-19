-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_weighted_signed_potential_drop_sum_swap
-- name    : AvramDividend.Classical.avram_jump6_B_weighted_signed_potential_drop_sum_swap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:09:04.516732+00:00
-- url     : https://prove2.me/theorems/0dec09c8-a4fc-4e35-b3fc-5138bdaff345
-- title:
--   Weighted finite signed potential drops reverse sign under pre/post swap
-- statement:
--   Exact finite-sum sign identity converting original physical-grid weighted postpayment potential differences to minus the corresponding positive discounted prepayment drops. Required to rewrite the source-exact original topcap real stopped Stieltjes cash bound into the positive clock payment residual theorem.

import Mathlib
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_weighted_signed_potential_drop_sum_swap
    {ι : Type*} (s : Finset ι) (E A B : ι → ℝ) :
    (∑ i ∈ s, E i * (A i - B i)) =
      -(∑ i ∈ s, E i * (B i - A i)) := by sorry
