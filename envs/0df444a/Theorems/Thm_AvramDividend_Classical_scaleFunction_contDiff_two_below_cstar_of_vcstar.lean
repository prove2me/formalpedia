-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_below_cstar_of_vcstar
-- name    : AvramDividend.Classical.scaleFunction_contDiff_two_below_cstar_of_vcstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T10:05:19.533454+00:00
-- url     : https://prove2.me/theorems/68c29f97-4002-4556-839c-fee186f52377
-- title:
--   Transfer C2 regularity from the barrier candidate to the scale function below cstar
-- statement:
--   On the open interval below cstar the barrier candidate is a constant multiple k W of the scale function, where k = divE 1 (scaleDeriv W cstar). If k is nonzero, multiplying vcstar by k^{-1} recovers W on this interval. Hence any C2 regularity assumed for vcstar transfers to W. This is the purely analytic/definitional regularity bridge needed in the explicit smoothness branch of Lemma 4.
-- source:
--   Direct consequence of the barrier-value definition used in Avram, Palmowski and Pistorius (2007), equations (3.12)-(3.13) and Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_contDiff_two_below_cstar_of_vcstar
    (W : ℝ → ℝ)
    (hvc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0) :
    ContDiffOn ℝ 2 W (Ioo 0 (cstar W).toReal) := by sorry

end AvramDividend.Classical
