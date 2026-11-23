-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_eta
-- name    : Formalism.FourierDecayAlt.P.G4.blk_eta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:39:07.729806+00:00
-- url     : https://prove2.me/theorems/655cc235-9142-4282-b51c-1c6b94d48fa4
-- title:
--   G4: blk eta
-- statement:
--   The G4 construction uses the blk eta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L64-L68

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

theorem Formalism.FourierDecayAlt.P.G4.blk_eta {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    M = blk (Matrix.of fun i j => M i.castSucc j.castSucc) (fun i => M i.castSucc (Fin.last n))
      (fun j => M (Fin.last n) j.castSucc) (M (Fin.last n) (Fin.last n)) := by sorry
