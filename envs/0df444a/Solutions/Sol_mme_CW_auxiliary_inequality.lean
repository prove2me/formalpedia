-- Prove2me | solution 1 for mme_CW_auxiliary_inequality
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:31:28.96201+00:00
-- url     : https://prove2.me/submissions/3321d741-d2c1-4b0e-a0f3-9c2b4202edd6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_CW_auxiliary_RHS_one_le
import Theorems.Thm_mme_CW_coupled_piece_value
import Theorems.Thm_mme_CW_square_laser_value_of_coupled
import Theorems.Thm_mme_CW_square_asymptoticRank_le
import Theorems.Thm_mme_tau_value_le_of_asymptoticRank_le

open MME

universe u

theorem solution
    {K : Type u} [Field K]
    (q : ℕ) (hq : 3 ≤ q)
    (homega : 2 ≤ matMulExp_strassen K)
    (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hnorm : 3 * a + 6 * b + 3 * c + 3 * d = 1) :
    auxiliaryRHS q (matMulExp_strassen K / 3) a b c d ≤
      ((q : ℝ) + 2) ^ (2 : ℕ) := by
  have htau : 2 ≤ 3 * (matMulExp_strassen K / 3) := by
    convert homega using 1 <;> ring
  have hcoupled := mme_CW_coupled_piece_value
    (K := K) q hq (matMulExp_strassen K / 3) htau
  have hvalue := mme_CW_square_laser_value_of_coupled
    (K := K) q hq (matMulExp_strassen K / 3) htau
    a b c d ha hb hc hd hnorm hcoupled
  exact mme_tau_value_le_of_asymptoticRank_le
    (by positivity)
    (mme_CW_auxiliary_RHS_one_le
      q hq (matMulExp_strassen K / 3) htau
      a b c d ha hb hc hd hnorm)
    (mme_CW_square_asymptoticRank_le (K := K) q)
    hvalue
