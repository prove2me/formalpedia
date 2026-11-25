-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_eventually_ne_zero_add
-- name    : Formalism.FourierDecayAlt.P.PBK.eventually_ne_zero_add
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:53:42.46077+00:00
-- url     : https://prove2.me/theorems/12220852-8f35-4cc7-867a-d97e62d3f20b
-- title:
--   PBK: eventually ne zero add
-- statement:
--   The PBK construction uses the eventually ne zero add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormOfMemRootSetOne.lean#L135-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormOfMemRootSetOne.lean#L135-L139

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

theorem Formalism.FourierDecayAlt.P.PBK.eventually_ne_zero_add (σ : ℂ) : ∀ᶠ x in cocompact ℂ, x ≠ 0 ∧ x + σ ≠ 0 := by sorry
