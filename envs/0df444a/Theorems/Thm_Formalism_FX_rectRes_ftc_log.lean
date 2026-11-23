-- Prove2me | Theorems.Thm_Formalism_FX_rectRes_ftc_log
-- name    : Formalism.FX.rectRes_ftc_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:12.865132+00:00
-- url     : https://prove2.me/theorems/5195b8ce-723e-44c9-ad53-e3f5aad7a2ee
-- title:
--   FX: rect Res ftc log
-- statement:
--   The FX construction uses the rect Res ftc log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/RectResidue.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/RectResidue.lean#L9-L15

import Definitions.Def_Formalism_LFunctionBounds_ExpSumLowerBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue
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
open Formalism Formalism.FX

theorem Formalism.FX.rectRes_ftc_log {γ : ℝ → ℂ} {d : ℂ} {a b : ℝ} (hγ : ∀ t, HasDerivAt γ d t)
    (hs : ∀ t ∈ Set.uIcc a b, γ t ∈ slitPlane) :
    ∫ t in a..b, d / γ t = log (γ b) - log (γ a) := by sorry
