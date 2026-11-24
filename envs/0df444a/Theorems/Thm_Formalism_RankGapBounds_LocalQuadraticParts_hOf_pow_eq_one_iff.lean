-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_hOf_pow_eq_one_iff
-- name    : Formalism.RankGapBounds.LocalQuadraticParts.hOf_pow_eq_one_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:25:48.221337+00:00
-- url     : https://prove2.me/theorems/b2ba426f-9e8b-409e-be96-6140c2315c23
-- title:
--   Local Quadratic Parts: h Of pow eq one iff
-- statement:
--   The Local Quadratic Parts construction uses the h Of pow eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FourNotDvdOddSqAddOne.lean#L101-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FourNotDvdOddSqAddOne.lean#L101-L123

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

theorem Formalism.RankGapBounds.LocalQuadraticParts.hOf_pow_eq_one_iff (e j l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)) :
    (hOf e l hl) ^ (2 ^ j) = 1 ↔
      ((((l : ℤ) ^ (2 ^ j) : ℤ) : ZMod (4 * 2 ^ e)) = 1 ∨
        (((l : ℤ) ^ (2 ^ j) : ℤ) : ZMod (4 * 2 ^ e)) = -1) := by sorry
