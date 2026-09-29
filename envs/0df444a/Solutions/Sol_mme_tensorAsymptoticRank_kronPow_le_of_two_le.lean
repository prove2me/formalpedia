-- Prove2me | solution 1 for mme_tensorAsymptoticRank_kronPow_le_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:29:31.727283+00:00
-- url     : https://prove2.me/submissions/0ebbc964-d1b2-496a-8d76-f45dcd6abdeb

import Theorems.Thm_mme_tensorAsymptoticRank_kronPow_eq_of_two_le_of_pos
import Theorems.Thm_mme_tensorAsymptoticRank_kronPow_zero_le

open MME

universe u

theorem solution
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    (X : TensorObj K d) (N : ℕ) :
    tensorAsymptoticRank (X.kronPow N) ≤ tensorAsymptoticRank X ^ N := by
  cases N with
  | zero =>
      exact mme_tensorAsymptoticRank_kronPow_zero_le X
  | succ n =>
      exact (mme_tensorAsymptoticRank_kronPow_eq_of_two_le_of_pos
        hd X (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).le
