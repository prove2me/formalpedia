-- Prove2me | solution 1 for mme_CW_coupled_piece_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:31:29.051072+00:00
-- url     : https://prove2.me/submissions/003714b2-7a15-4389-a551-fc28e390cea4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_CW_coupled_pruning_ratio
import Theorems.Thm_mme_CW_coupled_value_cube
import Theorems.Thm_mme_CW_coupled_raw_cyclic_value_of_ratio

open MME

universe u

theorem solution
    {K : Type u} [Field K]
    (q : ℕ) (hq : 3 ≤ q) (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    HasSymmetricTauValueAtLeast (coupledObj K q) tau
      ((2 : ℝ) ^ ((2 : ℝ) / 3) *
       (q : ℝ) ^ tau *
       (((q : ℝ) ^ (3 * tau) + 2) ^ ((1 : ℝ) / 3))) := by
  unfold HasSymmetricTauValueAtLeast
  rw [mme_CW_coupled_value_cube q hq tau]
  exact mme_CW_coupled_raw_cyclic_value_of_ratio
    q hq tau htau (mme_CW_coupled_pruning_ratio q hq tau htau)
