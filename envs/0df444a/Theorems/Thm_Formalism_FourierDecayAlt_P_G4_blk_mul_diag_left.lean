-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_mul_diag_left
-- name    : Formalism.FourierDecayAlt.P.G4.blk_mul_diag_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:37.224323+00:00
-- url     : https://prove2.me/theorems/6fd8d21e-f2a5-467f-84ec-22ae7586f279
-- title:
--   G4: blk mul diag left
-- statement:
--   The G4 construction uses the blk mul diag left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L353-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L353-L356

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4

theorem Formalism.FourierDecayAlt.P.G4.blk_mul_diag_left {n : ℕ} (A K : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) :
    blk K 0 0 1 * blk A b 0 1 = blk (K * A) (K *ᵥ b) 0 1 := by sorry
