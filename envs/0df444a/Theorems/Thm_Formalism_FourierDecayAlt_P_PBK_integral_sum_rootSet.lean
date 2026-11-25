-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_integral_sum_rootSet
-- name    : Formalism.FourierDecayAlt.P.PBK.integral_sum_rootSet
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:20:33.473363+00:00
-- url     : https://prove2.me/theorems/54999d61-9197-4669-9d04-27f0ecdce8df
-- title:
--   PBK: integral sum root Set
-- statement:
--   The PBK construction uses the integral sum root Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormOfMemRootSetOne.lean#L101-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormOfMemRootSetOne.lean#L101-L125

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
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem Formalism.FourierDecayAlt.P.PBK.integral_sum_rootSet (s : ℕ) (hs : s ≠ 0) (u : ℂ) (hu : u ≠ 0) (F : ℂ → E)
    (hF : Integrable (fun z => ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z)) :
    Integrable (fun c => ∑ z ∈ G.rootSet s (u * c), F z) ∧
      ∫ c, ∑ z ∈ G.rootSet s (u * c), F z = ∫ z, ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z := by sorry
