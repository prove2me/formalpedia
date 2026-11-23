-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_mul
-- name    : Formalism.FourierDecayAlt.P.Mx2.multiplierPair_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:54.175937+00:00
-- url     : https://prove2.me/theorems/3cf0e566-d725-4382-b59f-2a81d5f20eda
-- title:
--   Mx2: multiplier Pair mul
-- statement:
--   The Mx2 construction uses the multiplier Pair mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L65-L69

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

theorem Formalism.FourierDecayAlt.P.Mx2.multiplierPair_mul (f fb g gb : Fn r) : fnP f fb * fnP g gb = fnP (f * g) (fb * gb) := by sorry
