-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_odd_of_coprime
-- name    : Formalism.RankGapBounds.LocalQuadraticParts.odd_of_coprime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:06.720654+00:00
-- url     : https://prove2.me/theorems/2834dd39-d3da-4f14-8f8c-5c5ea256b6ef
-- title:
--   Local Quadratic Parts: odd of coprime
-- statement:
--   The Local Quadratic Parts construction uses the odd of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FourNotDvdOddSqAddOne.lean#L125-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FourNotDvdOddSqAddOne.lean#L125-L130

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

theorem Formalism.RankGapBounds.LocalQuadraticParts.odd_of_coprime (e l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)) : Odd (l : ℤ) := by sorry
