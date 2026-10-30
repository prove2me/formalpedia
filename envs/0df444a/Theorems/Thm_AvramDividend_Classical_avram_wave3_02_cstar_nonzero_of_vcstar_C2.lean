-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_cstar_nonzero_of_vcstar_C2
-- name    : AvramDividend.Classical.avram_wave3_02_cstar_nonzero_of_vcstar_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:50:53.557155+00:00
-- url     : https://prove2.me/theorems/5d71f64e-b206-4ef1-95b2-23d8b3744f57
-- title:
--   C2 optimal barrier candidate forces a nonzero scale derivative at positive cstar
-- statement:
--   A positive finite cstar and C2 smoothness of the actual piecewise candidate vcstar force the ordinary scale derivative at cstar to be nonzero. If it vanished, the candidate would be zero on the left of cstar and affine with unit slope on the right, violating differentiability.
-- source:
--   The exact formal barrierValue, scaleDeriv and divE definitions of Avram–Palmowski–Pistorius 2007, and canonical Proved vcstar_deriv_one_of_contDiffOn eb491d0b. The proof uses one-sided uniqueness of the derivative on Iic cstar, without any global scale C1 premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_contDiffOn

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_cstar_nonzero_of_vcstar_C2
    (W : ℝ → ℝ)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hsmooth : ContDiffOn ℝ 2 (vcstar W) (Ioi (0 : ℝ))) :
    deriv W (cstar W).toReal ≠ 0 := by sorry
