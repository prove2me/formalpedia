-- Prove2me | Theorems.Thm_Formalism_FX_rectRes_log_sub_log_neg_of_im_neg
-- name    : Formalism.FX.rectRes_log_sub_log_neg_of_im_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:32.778767+00:00
-- url     : https://prove2.me/theorems/4cbd2f02-4f01-42fa-9b6a-e7ed7d4ca30f
-- title:
--   FX: rect Res log sub log neg of im neg
-- statement:
--   The FX construction uses the rect Res log sub log neg of im neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/RectResidue.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/RectResidue.lean#L22-L25

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

theorem Formalism.FX.rectRes_log_sub_log_neg_of_im_neg {z : ℂ} (h : z.im < 0) :
    log z - log (-z) = -((Real.pi : ℂ) * I) := by sorry
