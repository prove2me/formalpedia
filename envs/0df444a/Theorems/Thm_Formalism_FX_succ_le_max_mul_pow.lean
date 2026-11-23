-- Prove2me | Theorems.Thm_Formalism_FX_succ_le_max_mul_pow
-- name    : Formalism.FX.succ_le_max_mul_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:23.218837+00:00
-- url     : https://prove2.me/theorems/d7691516-846f-44c2-a92c-8448a12c96bd
-- title:
--   FX: succ le max mul pow
-- statement:
--   The FX construction uses the succ le max mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/DivisorBound.lean#L18-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/DivisorBound.lean#L18-L30

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

theorem Formalism.FX.succ_le_max_mul_pow (e : ℝ) (he : 0 < e) (p k : ℕ) (hp : 2 ≤ p) :
    ((k : ℝ) + 1) ≤ max 1 (1 / (e * Real.log 2)) * ((p : ℝ) ^ e) ^ k := by sorry
