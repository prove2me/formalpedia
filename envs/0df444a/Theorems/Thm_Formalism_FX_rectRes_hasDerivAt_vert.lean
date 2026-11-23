-- Prove2me | Theorems.Thm_Formalism_FX_rectRes_hasDerivAt_vert
-- name    : Formalism.FX.rectRes_hasDerivAt_vert
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:14.873847+00:00
-- url     : https://prove2.me/theorems/f6d06634-fd33-486c-9d47-7d185d7127c8
-- title:
--   FX: rect Res has Deriv At vert
-- statement:
--   The FX construction uses the rect Res has Deriv At vert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/RectResidue.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/RectResidue.lean#L32-L35

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

theorem Formalism.FX.rectRes_hasDerivAt_vert (c : ℂ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => c + (y : ℂ) * I) I t := by sorry
