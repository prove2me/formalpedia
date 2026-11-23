-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_zmod_nat_eq_one_iff
-- name    : Formalism.RankGapBounds.LocalQuadraticParts.zmod_nat_eq_one_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:53.130641+00:00
-- url     : https://prove2.me/theorems/18a0a030-7e39-473a-b0c7-a4a4ae38126a
-- title:
--   Local Quadratic Parts: zmod nat eq one iff
-- statement:
--   The Local Quadratic Parts construction uses the zmod nat eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FourNotDvdOddSqAddOne.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FourNotDvdOddSqAddOne.lean#L11-L13

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

theorem Formalism.RankGapBounds.LocalQuadraticParts.zmod_nat_eq_one_iff (n l : ℕ) : ((l : ZMod n) = 1) ↔ (n : ℤ) ∣ (l : ℤ) - 1 := by sorry
