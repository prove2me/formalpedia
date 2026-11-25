-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_product_decay_summable
-- name    : Formalism.FourierDecayAlt.P.product_decay_summable
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:34:09.341316+00:00
-- url     : https://prove2.me/theorems/40eec37b-5ef4-4f7c-97fb-0562a0aaf2e5
-- title:
--   P: product decay summable
-- statement:
--   The P construction uses the product decay summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonSummationDecay.lean#L290-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonSummationDecay.lean#L290-L290

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

theorem Formalism.FourierDecayAlt.P.product_decay_summable : Formalism.FourierDecayAlt.F7.ProductDecaySummable := by sorry
