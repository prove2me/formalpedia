-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_zeta_free_of_variable
-- name    : Formalism.FourierDecayAlt.P.Mx2.zeta_free_of_variable
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:36.717838+00:00
-- url     : https://prove2.me/theorems/b10d9e78-6805-4aad-aa98-1a640b0f64e2
-- title:
--   Mx2: zeta free of variable
-- statement:
--   The Mx2 construction uses the zeta free of variable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L271-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L271-L271

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

theorem Formalism.FourierDecayAlt.P.Mx2.zeta_free_of_variable : ZF (coord vz : Fn r) := by sorry
