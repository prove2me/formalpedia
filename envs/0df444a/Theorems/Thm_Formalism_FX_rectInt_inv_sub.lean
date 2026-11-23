-- Prove2me | Theorems.Thm_Formalism_FX_rectInt_inv_sub
-- name    : Formalism.FX.rectInt_inv_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:11.358433+00:00
-- url     : https://prove2.me/theorems/51c2288a-86ea-4a69-9db2-911fda873109
-- title:
--   FX: rect Int inv sub
-- statement:
--   The FX construction uses the rect Int inv sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/RectResidue.lean#L37-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/RectResidue.lean#L37-L87

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

theorem Formalism.FX.rectInt_inv_sub (p : ℂ) (x0 x1 y0 y1 : ℝ) (h1 : x0 < p.re) (h2 : p.re < x1)
    (h3 : y0 < p.im) (h4 : p.im < y1) :
    rectInt (fun w => 1 / (w - p)) x0 x1 y0 y1 = 2 * (Real.pi : ℂ) * I := by sorry
