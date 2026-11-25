-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_shift_ne
-- name    : Formalism.FourierDecayAlt.P.PBK.tendsto_shift_ne
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:24:31.742175+00:00
-- url     : https://prove2.me/theorems/e7ed49d6-7696-4840-a9f1-6ab42681e5e4
-- title:
--   PBK: tendsto shift ne
-- statement:
--   The PBK construction uses the tendsto shift ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormOfMemRootSetOne.lean#L223-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormOfMemRootSetOne.lean#L223-L250

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

theorem Formalism.FourierDecayAlt.P.PBK.tendsto_shift_ne (s : ℕ) (hs : 1 ≤ s) (σ ζ : ℂ) (hζ : ζ ≠ 1) :
    Tendsto (fun x => ζ * rhoR s σ x * (x + σ) - x) (cocompact ℂ) (cocompact ℂ) := by sorry
