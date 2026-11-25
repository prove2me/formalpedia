-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_poisson_series_summable
-- name    : Formalism.FourierDecayAlt.P.poisson_series_summable
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:39.174271+00:00
-- url     : https://prove2.me/theorems/1823ddb8-6ce9-544b-9d71-9cacd5ffce4b
-- title:
--   P: poisson series summable
-- statement:
--   The P construction uses the poisson series summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonSummationDecay.lean#L288-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonSummationDecay.lean#L288-L288

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.poisson_series_summable : Formalism.FourierDecayAlt.F7.PoissonSummable := by sorry
