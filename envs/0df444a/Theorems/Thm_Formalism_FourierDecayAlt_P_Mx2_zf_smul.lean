-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_zf_smul
-- name    : Formalism.FourierDecayAlt.P.Mx2.zf_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:58.699824+00:00
-- url     : https://prove2.me/theorems/8731bb0e-6494-4ceb-897d-d6b0d4b433fc
-- title:
--   Mx2: zf smul
-- statement:
--   The Mx2 construction uses the zf smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L281-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L281-L282

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx2
variable {r : ℕ}

theorem Formalism.FourierDecayAlt.P.Mx2.zf_smul {f : Fn r} (z : ℂ) (hf : ZF f) : ZF (z • f) := by sorry
