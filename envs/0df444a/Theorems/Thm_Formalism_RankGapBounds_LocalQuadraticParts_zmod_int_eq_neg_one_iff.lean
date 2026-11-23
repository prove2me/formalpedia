-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_zmod_int_eq_neg_one_iff
-- name    : Formalism.RankGapBounds.LocalQuadraticParts.zmod_int_eq_neg_one_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:53.056013+00:00
-- url     : https://prove2.me/theorems/4a444fb4-b08e-4558-bd82-b14c8a5a10ba
-- title:
--   Local Quadratic Parts: zmod int eq neg one iff
-- statement:
--   The Local Quadratic Parts construction uses the zmod int eq neg one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FourNotDvdOddSqAddOne.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FourNotDvdOddSqAddOne.lean#L8-L9

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

theorem Formalism.RankGapBounds.LocalQuadraticParts.zmod_int_eq_neg_one_iff (n : ℕ) (x : ℤ) : ((x : ZMod n) = -1) ↔ (n : ℤ) ∣ x + 1 := by sorry
