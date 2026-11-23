-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_zmod_nat_eq_neg_one_iff
-- name    : Formalism.RankGapBounds.LocalQuadraticParts.zmod_nat_eq_neg_one_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:53.205856+00:00
-- url     : https://prove2.me/theorems/187ded88-0fde-428c-91ac-883c90bb4a03
-- title:
--   Local Quadratic Parts: zmod nat eq neg one iff
-- statement:
--   The Local Quadratic Parts construction uses the zmod nat eq neg one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FourNotDvdOddSqAddOne.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FourNotDvdOddSqAddOne.lean#L15-L17

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

theorem Formalism.RankGapBounds.LocalQuadraticParts.zmod_nat_eq_neg_one_iff (n l : ℕ) : ((l : ZMod n) = -1) ↔ (n : ℤ) ∣ (l : ℤ) + 1 := by sorry
