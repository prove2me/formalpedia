-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_memLp_comp_mul
-- name    : Formalism.FourierDecayAlt.P.PBK.memLp_comp_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:52:35.849598+00:00
-- url     : https://prove2.me/theorems/b7e3cc3f-279b-4585-bea5-f6134e667953
-- title:
--   PBK: mem Lp comp mul
-- statement:
--   The PBK construction uses the mem Lp comp mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastBlockDecay.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastBlockDecay.lean#L44-L49

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

theorem Formalism.FourierDecayAlt.P.PBK.memLp_comp_mul {p : ENNReal} {f : ℂ → E} (hf : MemLp f p volume) (ρ : ℂ) (hρ : ρ ≠ 0) :
    MemLp (fun z => f (ρ * z)) p volume := by sorry
