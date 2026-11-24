-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_pm_key_Y
-- name    : Formalism.RankGapBounds.LocalQuadraticParts.pm_key_Y
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:26:05.049727+00:00
-- url     : https://prove2.me/theorems/c93e3da7-d267-4244-a410-7cfc369384e1
-- title:
--   Local Quadratic Parts: pm key Y
-- statement:
--   The Local Quadratic Parts construction uses the pm key Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/PmModulusFacts.lean#L83-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/PmModulusFacts.lean#L83-L94

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts
open Finset

theorem Formalism.RankGapBounds.LocalQuadraticParts.pm_key_Y (m x y Y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (h1 : x * y / 2 ≤ m) (hmY : m ≤ Y)
    (hm1 : 1 ≤ m) : Real.log m / m ≤ Real.log Y * (2 / y) * (1 / x) := by sorry
