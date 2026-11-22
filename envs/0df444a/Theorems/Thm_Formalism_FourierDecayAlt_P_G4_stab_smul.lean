-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_stab_smul
-- name    : Formalism.FourierDecayAlt.P.G4.stab_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:45:33.385422+00:00
-- url     : https://prove2.me/theorems/fb2ec52d-6a3f-4d36-86c4-98b5b0b470d6
-- title:
--   G4: stab smul
-- statement:
--   The G4 construction uses the stab smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L329-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L329-L332

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

theorem Formalism.FourierDecayAlt.P.G4.stab_smul {d : ℕ} {z : ℂ} (hz : z ≠ 0) (l u : Matrix (Fin d) (Fin d) ℂ) :
    l * (z • wMat d) * u = z • wMat d ↔ l * wMat d * u = wMat d := by sorry
