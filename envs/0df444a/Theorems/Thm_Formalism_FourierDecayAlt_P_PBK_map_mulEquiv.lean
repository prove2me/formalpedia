-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_map_mulEquiv
-- name    : Formalism.FourierDecayAlt.P.PBK.map_mulEquiv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:54:52.25631+00:00
-- url     : https://prove2.me/theorems/7e434db3-6b9f-5e8d-8747-221977d73f0f
-- title:
--   PBK: map mul Equiv
-- statement:
--   The PBK construction uses the map mul Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastBlockDecay.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastBlockDecay.lean#L30-L34

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

theorem Formalism.FourierDecayAlt.P.PBK.map_mulEquiv (ρ : ℂ) (hρ : ρ ≠ 0) :
    Measure.map (mulEquiv ρ hρ) volume = ENNReal.ofReal ((‖ρ‖ ^ 2)⁻¹) • (volume : Measure ℂ) := by sorry
