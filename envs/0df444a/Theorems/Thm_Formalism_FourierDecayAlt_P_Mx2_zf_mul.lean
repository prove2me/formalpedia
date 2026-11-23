-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_zf_mul
-- name    : Formalism.FourierDecayAlt.P.Mx2.zf_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:49.67825+00:00
-- url     : https://prove2.me/theorems/cb4b50d6-0f34-436a-b780-5c9002e06479
-- title:
--   Mx2: zf mul
-- statement:
--   The Mx2 construction uses the zf mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L279-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L279-L280

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

theorem Formalism.FourierDecayAlt.P.Mx2.zf_mul {f g : Fn r} (hf : ZF f) (hg : ZF g) : ZF (f * g) := by sorry
