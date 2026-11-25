-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_memLp_dil
-- name    : Formalism.FourierDecayAlt.P.PBK.memLp_dil
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:52:57.510795+00:00
-- url     : https://prove2.me/theorems/ee7e404b-d600-4d38-9ec1-da1480f9917b
-- title:
--   PBK: mem Lp dil
-- statement:
--   The PBK construction uses the mem Lp dil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastBlockDecay.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastBlockDecay.lean#L60-L62

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

theorem Formalism.FourierDecayAlt.P.PBK.memLp_dil {f : ℂ → E} (hf : MemLp f 2 volume) (ρ : ℂ) (hρ : ρ ≠ 0) :
    MemLp (fun z => ‖ρ‖ • f (ρ * z)) 2 volume := by sorry
