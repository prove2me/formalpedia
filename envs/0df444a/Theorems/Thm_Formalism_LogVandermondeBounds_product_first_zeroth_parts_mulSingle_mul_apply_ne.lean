-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_mulSingle_mul_apply_ne
-- name    : Formalism.LogVandermondeBounds.product_first_zeroth_parts.mulSingle_mul_apply_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:40:18.355803+00:00
-- url     : https://prove2.me/theorems/d5a9110f-9ed9-41df-b0a2-12f1ad598e3c
-- title:
--   product first zeroth parts: mul Single mul apply ne
-- statement:
--   The product first zeroth parts construction uses the mul Single mul apply ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/MulSingleMulApplySelf.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/MulSingleMulApplySelf.lean#L16-L18

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_MulSingleMulApplySelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
variable {ι H K : Type} [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [DecidableEq H] [Field K]
omit [Fintype H]

theorem Formalism.LogVandermondeBounds.product_first_zeroth_parts.mulSingle_mul_apply_ne (v w : ι) (c : H) (h : ι → H) (hw : w ≠ v) :
    ((Pi.mulSingle v c : ι → H) * h) w = h w := by sorry
