-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_two_of_vcstar_nonzero
-- name    : AvramDividend.Classical.scaleFunction_contDiffOn_two_of_vcstar_nonzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:11:42.281699+00:00
-- url     : https://prove2.me/theorems/7b4c19f9-8cee-47ec-81b9-d1ca699be15d
-- title:
--   C2 regularity transfers from vcstar to W below cstar when the scale factor is nonzero
-- statement:
--   Let a=(cstar W).toReal and k=divE 1 (scaleDeriv W a). On (0,a), the barrier candidate vcstar W is exactly k·W by the lower branch of barrierValue. If k is nonzero, W=k⁻¹·vcstar W on this interval. Therefore C² regularity of vcstar W on (0,a) implies C² regularity of W there. This is the regularity-transfer step needed in the explicit smoothness branch of Lemma 4.
-- source:
--   Directly from the definitions of vcstar, barrierValue and divE; used in the formalisation of Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_contDiffOn_two_of_vcstar_nonzero
    (W : ℝ → ℝ)
    (hvc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0) :
    ContDiffOn ℝ 2 W (Ioo 0 (cstar W).toReal) := by sorry

end AvramDividend.Classical
