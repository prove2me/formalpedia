-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_integrable_sq_of_memLp
-- name    : Formalism.FourierDecayAlt.P.PBK.integrable_sq_of_memLp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:52:13.259576+00:00
-- url     : https://prove2.me/theorems/995bbb83-5930-45b1-95d1-190550bf91aa
-- title:
--   PBK: integrable sq of mem Lp
-- statement:
--   The PBK construction uses the integrable sq of mem Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastBlockDecay.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastBlockDecay.lean#L64-L65

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

theorem Formalism.FourierDecayAlt.P.PBK.integrable_sq_of_memLp {u : ℂ → E} (hu : MemLp u 2 volume) : Integrable (fun z => ‖u z‖ ^ 2) volume := by sorry
