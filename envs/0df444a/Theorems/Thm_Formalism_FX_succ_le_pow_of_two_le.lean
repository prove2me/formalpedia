-- Prove2me | Theorems.Thm_Formalism_FX_succ_le_pow_of_two_le
-- name    : Formalism.FX.succ_le_pow_of_two_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:20.919532+00:00
-- url     : https://prove2.me/theorems/3df45675-05fb-4366-8a13-2d0f3b0faacc
-- title:
--   FX: succ le pow of two le
-- statement:
--   The FX construction uses the succ le pow of two le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/DivisorBound.lean#L32-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/DivisorBound.lean#L32-L43

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_DivisorBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FX
open Finset

theorem Formalism.FX.succ_le_pow_of_two_le (e : ℝ) (p k : ℕ) (hp : 2 ≤ (p : ℝ) ^ e) :
    ((k : ℝ) + 1) ≤ ((p : ℝ) ^ e) ^ k := by sorry
