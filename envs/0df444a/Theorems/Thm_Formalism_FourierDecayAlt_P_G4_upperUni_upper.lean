-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upperUni_upper
-- name    : Formalism.FourierDecayAlt.P.G4.upperUni_upper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:14.731237+00:00
-- url     : https://prove2.me/theorems/9982e756-69c0-4591-bf6b-c8ae927f050c
-- title:
--   G4: upper Uni upper
-- statement:
--   The G4 construction uses the upper Uni upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L201-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L201-L204

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

theorem Formalism.FourierDecayAlt.P.G4.upperUni_upper {d : ℕ} (v : UT d → ℂ) : IsUpperUni (upper v) := by sorry
