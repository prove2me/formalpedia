-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_vc_inj
-- name    : Formalism.FourierDecayAlt.P.Mx2.vc_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:27.364034+00:00
-- url     : https://prove2.me/theorems/4cce309e-b27e-44f9-8391-02a4f290438c
-- title:
--   Mx2: vc inj
-- statement:
--   The Mx2 construction uses the vc inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L238-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L238-L241

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

theorem Formalism.FourierDecayAlt.P.Mx2.vc_inj (l m : Fin r) : (vc l : Var r) = vc m ↔ l = m := by sorry
