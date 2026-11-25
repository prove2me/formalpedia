-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_dil_cpt
-- name    : Formalism.FourierDecayAlt.P.PBK.tendsto_dil_cpt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:51:54.816279+00:00
-- url     : https://prove2.me/theorems/f4530f98-4695-50a4-ad2d-c78d114af465
-- title:
--   PBK: tendsto dil cpt
-- statement:
--   The PBK construction uses the tendsto dil cpt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastBlockDecay.lean#L67-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastBlockDecay.lean#L67-L135

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Formalism.FourierDecayAlt.P.PBK.tendsto_dil_cpt (g : ℂ → E) (hgc : Continuous g) (hgs : HasCompactSupport g) (ζ : ℂ) (hζ : ζ ≠ 0) :
    Tendsto (fun ρ : ℂ => ∫ z, ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2) (𝓝 ζ) (𝓝 0) := by sorry
