-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_mulEquiv_apply
-- name    : Formalism.FourierDecayAlt.P.PBK.mulEquiv_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:51:45.581656+00:00
-- url     : https://prove2.me/theorems/a62cb4a1-d417-554c-9f6f-d4ba4c13df6d
-- title:
--   PBK: mul Equiv apply
-- statement:
--   The PBK construction uses the mul Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastBlockDecay.lean#L28-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastBlockDecay.lean#L28-L28

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

theorem Formalism.FourierDecayAlt.P.PBK.mulEquiv_apply (ρ : ℂ) (hρ : ρ ≠ 0) (z : ℂ) : mulEquiv ρ hρ z = ρ * z := by sorry
