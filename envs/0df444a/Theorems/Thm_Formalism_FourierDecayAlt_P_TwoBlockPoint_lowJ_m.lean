-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_lowJ_m
-- name    : Formalism.FourierDecayAlt.P.TwoBlockPoint.lowJ_m
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:15.953193+00:00
-- url     : https://prove2.me/theorems/066dc75d-ea12-491f-a381-ac7780743751
-- title:
--   Two Block Point: low J m
-- statement:
--   The Two Block Point construction uses the low J m property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoBlockPoint.lean#L630-L631
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoBlockPoint.lean#L630-L631

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoBlockPoint
variable {K : Type} [CommRing K] {h g w : Point K} (hN : w.1.sum = h.1.sum + g.1.sum)
  (hW : pt w.1 w.2 = blkM hN (pt h.1 h.2) 0 0 (pt g.1 g.2))

theorem Formalism.FourierDecayAlt.P.TwoBlockPoint.lowJ_m (v : lowW K h.1 h.2 × lowW K g.1 g.2) (X : Matrix (Fin g.1.sum) (Fin h.1.sum) K) :
    sec_m (lowJ hN hW v X) = blkM hN (sec_m v.1) 0 (X * sec_m v.1) (sec_m v.2) := by sorry
