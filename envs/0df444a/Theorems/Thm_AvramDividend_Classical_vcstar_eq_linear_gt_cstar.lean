-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_eq_linear_gt_cstar
-- name    : AvramDividend.Classical.vcstar_eq_linear_gt_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:16:38.774612+00:00
-- url     : https://prove2.me/theorems/ee11c526-1dfc-4622-86fb-5de4518a7c45
-- title:
--   Optimal barrier candidate equals its linear continuation above c-star
-- statement:
--   For any real scale-function candidate W and any capital z strictly above the real optimal barrier c-star, the barrier candidate equals z−c-star plus the value of the scaled W branch at the barrier. This source-level piecewise identity shows that the candidate has unit slope on the strictly upper branch, and isolates the above-barrier portion needed in C1 and weighted-jet matching proofs.
-- source:
--   Definitional equation for vcstar and the linear branch of barrierValue from Definitions.Def_AvramDividend_Classical_ScaleFunction; complements vcstar_eq_scaledW_le_cstar.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_eq_linear_gt_cstar
    (W : ℝ → ℝ) (z : ℝ) (hz : (cstar W).toReal < z) :
    vcstar W z =
      z - (cstar W).toReal +
        divE (W (cstar W).toReal) (scaleDeriv W (cstar W).toReal) := by sorry
