-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_finrankFiberSumZero
-- name    : Formalism.LogVandermondeBounds.product_first_zeroth_parts.finrankFiberSumZero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:39:51.567799+00:00
-- url     : https://prove2.me/theorems/b61ebad1-59f4-44af-bc5e-e38cd0af194e
-- title:
--   product first zeroth parts: finrank Fiber Sum Zero
-- statement:
--   The product first zeroth parts construction uses the finrank Fiber Sum Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/MulSingleMulApplySelf.lean#L204-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/MulSingleMulApplySelf.lean#L204-L209

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

theorem Formalism.LogVandermondeBounds.product_first_zeroth_parts.finrankFiberSumZero : FinrankFiberSumZero := by sorry
