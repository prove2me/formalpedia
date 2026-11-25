-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_card_rootSet_le
-- name    : Formalism.FourierDecayAlt.P.PBK.card_rootSet_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:22:05.70387+00:00
-- url     : https://prove2.me/theorems/3582185b-0b1a-4240-844e-3c350a4c3226
-- title:
--   PBK: card root Set le
-- statement:
--   The PBK construction uses the card root Set le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AestronglyMeasurableMainD.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AestronglyMeasurableMainD.lean#L85-L87

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AestronglyMeasurableMainD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem Formalism.FourierDecayAlt.P.PBK.card_rootSet_le (s : ℕ) (a : ℂ) : (G.rootSet s a).card ≤ s := by sorry
