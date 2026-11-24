-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_sq_sub_one_dvd_iff
-- name    : Formalism.RankGapBounds.LocalQuadraticParts.sq_sub_one_dvd_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:25:26.233769+00:00
-- url     : https://prove2.me/theorems/d3128050-9d25-408d-a625-f83585467984
-- title:
--   Local Quadratic Parts: sq sub one dvd iff
-- statement:
--   The Local Quadratic Parts construction uses the sq sub one dvd iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FourNotDvdOddSqAddOne.lean#L26-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FourNotDvdOddSqAddOne.lean#L26-L56

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts

theorem Formalism.RankGapBounds.LocalQuadraticParts.sq_sub_one_dvd_iff (x : ℤ) (hx : Odd x) (m : ℕ) (hm : 1 ≤ m) :
    (2 : ℤ) ^ (m + 1) ∣ x ^ 2 - 1 ↔ ((2 : ℤ) ^ m ∣ x - 1 ∨ (2 : ℤ) ^ m ∣ x + 1) := by sorry
