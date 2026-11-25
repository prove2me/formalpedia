-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_abar_nonneg
-- name    : Formalism.FourierDecayAlt.P.PBK.abar_nonneg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:22:07.844975+00:00
-- url     : https://prove2.me/theorems/0714f602-2d49-475d-9d5a-ea3b2c1fb059
-- title:
--   PBK: abar nonneg
-- statement:
--   The PBK construction uses the abar nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AestronglyMeasurableMainD.lean#L18-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AestronglyMeasurableMainD.lean#L18-L18

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

theorem Formalism.FourierDecayAlt.P.PBK.abar_nonneg (s : ℕ) (ε : ℂ) (bt : ℂ → H) (D : ℂ) : 0 ≤ abar s ε bt D := by sorry
