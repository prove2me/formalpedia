-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_bz_indicator
-- name    : Formalism.FourierDecayAlt.P.PBK.bz_indicator
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:22:55.825616+00:00
-- url     : https://prove2.me/theorems/e6f27f6c-bc4f-4000-a76d-d8b2feb0a4a8
-- title:
--   PBK: bz indicator
-- statement:
--   The PBK construction uses the bz indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AestronglyMeasurableMainD.lean#L175-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AestronglyMeasurableMainD.lean#L175-L180

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
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Formalism.FourierDecayAlt.P.PBK.bz_indicator (s : ℕ) (bt : ℂ → H) (Qz : Set ℂ) :
    bz s (Qz.indicator bt) = Qz.indicator (bz s bt) := by sorry
