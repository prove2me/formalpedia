-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_units_zpow_neg_one_iff
-- name    : Formalism.RankGapBounds.LocalQuadraticParts.units_zpow_neg_one_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:25:36.782526+00:00
-- url     : https://prove2.me/theorems/ffbacf6e-bf57-4a68-bafd-a385fd4a8649
-- title:
--   Local Quadratic Parts: units zpow neg one iff
-- statement:
--   The Local Quadratic Parts construction uses the units zpow neg one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FourNotDvdOddSqAddOne.lean#L90-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FourNotDvdOddSqAddOne.lean#L90-L99

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

theorem Formalism.RankGapBounds.LocalQuadraticParts.units_zpow_neg_one_iff (n : ℕ) (u : (ZMod n)ˣ) :
    (∃ k : ℤ, (-1 : (ZMod n)ˣ) ^ k = u) ↔ (u = 1 ∨ u = -1) := by sorry
