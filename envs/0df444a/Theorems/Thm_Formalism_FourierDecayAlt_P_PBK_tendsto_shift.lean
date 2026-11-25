-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_shift
-- name    : Formalism.FourierDecayAlt.P.PBK.tendsto_shift
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:24:04.294167+00:00
-- url     : https://prove2.me/theorems/a9969475-6971-5622-8446-47cdc7916a6d
-- title:
--   PBK: tendsto shift
-- statement:
--   The PBK construction uses the tendsto shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormOfMemRootSetOne.lean#L188-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormOfMemRootSetOne.lean#L188-L221

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology Set Polynomial
noncomputable section
open Classical

theorem Formalism.FourierDecayAlt.P.PBK.tendsto_shift (s : ℕ) (hs : 1 ≤ s) (σ : ℂ) :
    Tendsto (fun x => (s : ℂ) * (rhoR s σ x * (x + σ) - x)) (cocompact ℂ) (𝓝 σ) := by sorry
