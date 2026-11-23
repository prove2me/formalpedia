-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_neg
-- name    : Formalism.FourierDecayAlt.P.Mx2.multiplierPair_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:23.798384+00:00
-- url     : https://prove2.me/theorems/95a9570f-5ea0-4427-8a2c-c1e20d3a5633
-- title:
--   Mx2: multiplier Pair neg
-- statement:
--   The Mx2 construction uses the multiplier Pair neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L81-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L81-L88

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

theorem Formalism.FourierDecayAlt.P.Mx2.multiplierPair_neg (f fb : Fn r) : -fnP f fb = fnP (-f) (-fb) := by sorry
