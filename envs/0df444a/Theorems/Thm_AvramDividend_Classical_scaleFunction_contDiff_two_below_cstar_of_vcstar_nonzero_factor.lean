-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_below_cstar_of_vcstar_nonzero_factor
-- name    : AvramDividend.Classical.scaleFunction_contDiff_two_below_cstar_of_vcstar_nonzero_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T11:22:47.462849+00:00
-- url     : https://prove2.me/theorems/4156fc94-8f91-4467-81cf-82983c35706e
-- title:
--   C2 regularity transfers from vcstar to the scale function below cstar
-- statement:
--   Let a=(cstar W).toReal and k=divE 1 (scaleDeriv W a). On the open interval (0,a), the barrier-value definition gives vcstar W x = k W x. If k is nonzero and vcstar W is C2 on (0,a), then W is C2 there as well, since W = k^{-1} vcstar W on that interval. This isolates the elementary regularity-transfer step used in the explicit-smoothness branch of Lemma 4.
-- source:
--   Avram, Palmowski and Pistorius (2007), proof of Lemma 4 together with the definition of the barrier value function.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_contDiff_two_below_cstar_of_vcstar_nonzero_factor
    (W : ℝ → ℝ)
    (hvc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0) :
    ContDiffOn ℝ 2 W (Ioo 0 (cstar W).toReal) := by sorry
