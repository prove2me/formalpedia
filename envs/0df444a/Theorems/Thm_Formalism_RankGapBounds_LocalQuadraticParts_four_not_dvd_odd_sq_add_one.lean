-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_four_not_dvd_odd_sq_add_one
-- name    : Formalism.RankGapBounds.LocalQuadraticParts.four_not_dvd_odd_sq_add_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:25:46.0198+00:00
-- url     : https://prove2.me/theorems/dc5948a5-5f94-4e6e-94c1-e736b7a70cf0
-- title:
--   Local Quadratic Parts: four not dvd odd sq add one
-- statement:
--   The Local Quadratic Parts construction uses the four not dvd odd sq add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FourNotDvdOddSqAddOne.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FourNotDvdOddSqAddOne.lean#L19-L24

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

theorem Formalism.RankGapBounds.LocalQuadraticParts.four_not_dvd_odd_sq_add_one (y : ℤ) (hy : Odd y) : ¬ (4 : ℤ) ∣ y ^ 2 + 1 := by sorry
