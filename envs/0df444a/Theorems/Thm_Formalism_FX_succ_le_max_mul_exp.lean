-- Prove2me | Theorems.Thm_Formalism_FX_succ_le_max_mul_exp
-- name    : Formalism.FX.succ_le_max_mul_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:31.235162+00:00
-- url     : https://prove2.me/theorems/60569f9a-de81-4573-969a-7b71f0f84c69
-- title:
--   FX: succ le max mul exp
-- statement:
--   The FX construction uses the succ le max mul exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/DivisorBound.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/DivisorBound.lean#L7-L16

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

theorem Formalism.FX.succ_le_max_mul_exp (a : ℝ) (ha : 0 < a) (k : ℕ) :
    ((k : ℝ) + 1) ≤ max 1 (1 / a) * Real.exp (a * k) := by sorry
