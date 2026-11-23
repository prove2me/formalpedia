-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_sum_eps
-- name    : Formalism.LogVandermondeBounds.product_first_zeroth_parts.sum_eps
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:30.487273+00:00
-- url     : https://prove2.me/theorems/2dec2b46-01ca-4031-be14-5ac5c2780aaa
-- title:
--   product first zeroth parts: sum eps
-- statement:
--   The product first zeroth parts construction uses the sum eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/MulSingleMulApplySelf.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/MulSingleMulApplySelf.lean#L25-L36

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

theorem Formalism.LogVandermondeBounds.product_first_zeroth_parts.sum_eps (a t : H) (ha : a ≠ 1) : ∑ c : H, (eps a (c * t) : K) = 0 := by sorry
