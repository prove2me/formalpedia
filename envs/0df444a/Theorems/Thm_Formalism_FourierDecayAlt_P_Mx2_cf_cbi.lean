-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_cf_cbi
-- name    : Formalism.FourierDecayAlt.P.Mx2.cf_cbi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:36.638805+00:00
-- url     : https://prove2.me/theorems/bd884240-3ed7-42ec-891a-d037f4847a26
-- title:
--   Mx2: cf cbi
-- statement:
--   The Mx2 construction uses the cf cbi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L287-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L287-L287

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

theorem Formalism.FourierDecayAlt.P.Mx2.cf_cbi (m : Fin r) : CF ((coord (vcb m))⁻¹ : Fn r) := by sorry
