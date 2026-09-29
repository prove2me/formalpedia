-- Prove2me | solution 1 for mme_omega_lt_CW
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-31T17:31:08.180667+00:00
-- url     : https://prove2.me/submissions/c718fb24-589e-4b84-ac27-7b5d3c0dcfb9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_omega_eq_strassen
import Theorems.Thm_mme_omega_le_of_subrank_capacity
import Theorems.Thm_mme_CW_subrank_capacity_lower
import Theorems.Thm_mme_CW_border_rank_le
import Theorems.Thm_mme_CW_numeric_optimum
import Theorems.Thm_mme_degenerates_asymptoticRank_le
import Definitions.Def_mme_omega
import Definitions.Def_mme_CW_tensor

open MME

universe u

theorem solution {K : Type u} [Field K] : matMulExp K < 2376 / 1000 := by
  have hR : tensorAsymptoticRank (CWObj K 6) ≤ (8 : ℝ) := by
    have h := mme_degenerates_asymptoticRank_le (mme_CW_border_rank_le (K := K) 6)
    exact_mod_cast h
  have hRpos : (1 : ℝ) ≤ (8 : ℝ) := by norm_num
  have hV : (1 : ℝ) < (5 : ℝ) / 2 := by norm_num
  have hsub : (5 : ℝ) / 2 ≤ subrankCapacity (CWObj K 6) :=
    mme_CW_subrank_capacity_lower
  have hbridge : matMulExp_strassen K ≤ Real.log 8 / Real.log (5 / 2) :=
    mme_omega_le_of_subrank_capacity hR hRpos hV hsub
  have hnum : Real.log 8 / Real.log (5 / 2) < 2376 / 1000 :=
    mme_CW_numeric_optimum
  calc matMulExp K
      = matMulExp_strassen K               := mme_omega_eq_strassen
    _ ≤ Real.log 8 / Real.log (5 / 2)      := hbridge
    _ < 2376 / 1000                        := hnum
