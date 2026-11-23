-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_mul_diag_right
-- name    : Formalism.FourierDecayAlt.P.G4.blk_mul_diag_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:55.906314+00:00
-- url     : https://prove2.me/theorems/4bf2474a-638e-4a60-98e6-6e331aa556cf
-- title:
--   G4: blk mul diag right
-- statement:
--   The G4 construction uses the blk mul diag right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L348-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L348-L351

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

theorem Formalism.FourierDecayAlt.P.G4.blk_mul_diag_right {n : ℕ} (A K : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ) :
    blk A 0 a 1 * blk K 0 0 1 = blk (A * K) 0 (a ᵥ* K) 1 := by sorry
