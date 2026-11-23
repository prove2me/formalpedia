-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_one
-- name    : Formalism.FourierDecayAlt.P.Mx2.multiplierPair_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:32.9608+00:00
-- url     : https://prove2.me/theorems/c54d4625-e112-4952-9b39-15a021d65a86
-- title:
--   Mx2: multiplier Pair one
-- statement:
--   The Mx2 construction uses the multiplier Pair one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L75-L80

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

theorem Formalism.FourierDecayAlt.P.Mx2.multiplierPair_one : (fnP 1 1 : Pr r) = 1 := by sorry
