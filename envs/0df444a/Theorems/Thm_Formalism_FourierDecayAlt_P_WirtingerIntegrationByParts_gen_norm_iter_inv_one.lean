-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_gen_norm_iter_inv_one
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.gen_norm_iter_inv_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:01.103052+00:00
-- url     : https://prove2.me/theorems/f6ee04fb-7ab8-43ab-8416-81561da7c75a
-- title:
--   Wirtinger Integration By Parts: gen norm iter inv one
-- statement:
--   The Wirtinger Integration By Parts construction uses the gen norm iter inv one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L418-L422
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L418-L422

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.gen_norm_iter_inv_one (i : ℕ) :
    ‖iteratedFDerivWithin ℝ i (Inv.inv : ℝ → ℝ) {0}ᶜ 1‖ = (i.factorial : ℝ) := by sorry
