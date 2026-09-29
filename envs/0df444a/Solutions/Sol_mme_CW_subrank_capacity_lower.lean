-- Prove2me | solution 1 for mme_CW_subrank_capacity_lower
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-31T17:44:40.492513+00:00
-- url     : https://prove2.me/submissions/2e59beb0-6d22-4201-b6d0-10994897423c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_CW_laser_witness
import Theorems.Thm_mme_laser_value_lower_bound

open MME

universe u

theorem solution {K : Type u} [Field K] :
    (5 : ℝ) / 2 ≤ subrankCapacity (CWObj K 6) := by
  obtain ⟨G, S, hSym, hsupport, hVal⟩ := mme_CW_laser_witness (K := K)
  have hAbs : laserValueFormula G S ≤ subrankCapacity (CWObj K 6) :=
    mme_laser_value_lower_bound G S hSym hsupport
  linarith
