-- Prove2me | Theorems.Thm_Formalism_ZF_rdp_seg
-- name    : Formalism.ZF.rdp_seg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:41:12.805395+00:00
-- url     : https://prove2.me/theorems/52d5dfe3-c078-427f-a5ce-c05519e5040c
-- title:
--   ZF: rdp seg
-- statement:
--   The ZF construction uses the rdp seg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RectDoublePole.lean#L88-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RectDoublePole.lean#L88-L101

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RectDoublePole
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZF

theorem Formalism.ZF.rdp_seg (g G : ℂ → ℂ) (a b p : ℂ) (γ : ℝ → ℂ) (s t : ℝ) (hγ : Continuous γ)
    (hG : ContinuousOn (fun u => G (γ u)) (Set.uIcc s t)) (hP : ∀ u ∈ Set.uIcc s t, γ u ≠ p)
    (hg : ∀ w : ℂ, w ≠ p → g w = G w + a / (w - p) ^ 2 + b / (w - p)) :
    IntervalIntegrable (fun u => g (γ u) - a / (γ u - p) ^ 2) MeasureTheory.volume s t ∧
    IntervalIntegrable (fun u => a / (γ u - p) ^ 2) MeasureTheory.volume s t := by sorry
