-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_bas_avoid
-- name    : Formalism.LogVandermondeBounds.product_first_zeroth_parts.bas_avoid
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:52:57.79667+00:00
-- url     : https://prove2.me/theorems/15a9367e-da9f-4a79-95fd-90f180304600
-- title:
--   product first zeroth parts: bas avoid
-- statement:
--   The product first zeroth parts construction uses the bas avoid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/MulSingleMulApplySelf.lean#L51-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/MulSingleMulApplySelf.lean#L51-L69

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

theorem Formalism.LogVandermondeBounds.product_first_zeroth_parts.bas_avoid (a b : ι → {c : H // c ≠ 1}) :
    (bas a (fun w => (b w : H)) : K) = if a = b then 1 else 0 := by sorry
