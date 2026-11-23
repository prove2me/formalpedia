-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_mulSingle_mul_apply_self
-- name    : Formalism.LogVandermondeBounds.product_first_zeroth_parts.mulSingle_mul_apply_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:40:27.174387+00:00
-- url     : https://prove2.me/theorems/026de696-e4a4-4e95-9522-a6e618ed4790
-- title:
--   product first zeroth parts: mul Single mul apply self
-- statement:
--   The product first zeroth parts construction uses the mul Single mul apply self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/MulSingleMulApplySelf.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/MulSingleMulApplySelf.lean#L21-L23

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

theorem Formalism.LogVandermondeBounds.product_first_zeroth_parts.mulSingle_mul_apply_self (v : ι) (c : H) (h : ι → H) :
    ((Pi.mulSingle v c : ι → H) * h) v = c * h v := by sorry
