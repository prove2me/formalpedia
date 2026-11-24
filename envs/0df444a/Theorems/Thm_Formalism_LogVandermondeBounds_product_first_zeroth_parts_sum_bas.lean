-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_sum_bas
-- name    : Formalism.LogVandermondeBounds.product_first_zeroth_parts.sum_bas
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:41.058621+00:00
-- url     : https://prove2.me/theorems/d00e559c-75ab-4f91-9446-a8e1cb81d4d0
-- title:
--   product first zeroth parts: sum bas
-- statement:
--   The product first zeroth parts construction uses the sum bas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/MulSingleMulApplySelf.lean#L38-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/MulSingleMulApplySelf.lean#L38-L49

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

theorem Formalism.LogVandermondeBounds.product_first_zeroth_parts.sum_bas (a : ι → {c : H // c ≠ 1}) (v : ι) (h : ι → H) :
    ∑ c : H, (bas a ((Pi.mulSingle v c : ι → H) * h) : K) = 0 := by sorry
