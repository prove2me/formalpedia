-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_nsq_eq
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_nsq_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:22.182243+00:00
-- url     : https://prove2.me/theorems/0d12eb8f-8647-483b-8e7c-0c4c5c2dc6aa
-- title:
--   Wirtinger Integration By Parts: bkb nsq eq
-- statement:
--   The Wirtinger Integration By Parts construction uses the bkb nsq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L559-L560
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L559-L560

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_nsq_eq (z : ℂ) : Complex.normSq z = Complex.reCLM ((starRingEnd ℂ) z • z) := by sorry
