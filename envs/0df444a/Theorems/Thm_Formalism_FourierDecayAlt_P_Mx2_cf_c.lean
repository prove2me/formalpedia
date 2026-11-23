-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_cf_c
-- name    : Formalism.FourierDecayAlt.P.Mx2.cf_c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:26.06881+00:00
-- url     : https://prove2.me/theorems/bce91d09-603b-402a-aab7-80fa22f442de
-- title:
--   Mx2: cf c
-- statement:
--   The Mx2 construction uses the cf c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L284-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L284-L284

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

theorem Formalism.FourierDecayAlt.P.Mx2.cf_c (m : Fin r) : CF (coord (vc m) : Fn r) := by sorry
