-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_map_mul_volume
-- name    : Formalism.FourierDecayAlt.P.PBK.map_mul_volume
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:07:34.821976+00:00
-- url     : https://prove2.me/theorems/89b7f880-3c73-5685-8561-eea4a5762b50
-- title:
--   PBK: map mul volume
-- statement:
--   The PBK construction uses the map mul volume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastBlockDecay.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastBlockDecay.lean#L14-L24

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

theorem Formalism.FourierDecayAlt.P.PBK.map_mul_volume (ρ : ℂ) (hρ : ρ ≠ 0) :
    Measure.map (fun z : ℂ => ρ * z) volume = ENNReal.ofReal ((‖ρ‖ ^ 2)⁻¹) • (volume : Measure ℂ) := by sorry
