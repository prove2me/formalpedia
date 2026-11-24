-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_pm_modulus_facts
-- name    : Formalism.RankGapBounds.LocalQuadraticParts.pm_modulus_facts
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:25:55.833801+00:00
-- url     : https://prove2.me/theorems/7a35f6c4-aee2-496a-85d8-44dfc647e83d
-- title:
--   Local Quadratic Parts: pm modulus facts
-- statement:
--   The Local Quadratic Parts construction uses the pm modulus facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/PmModulusFacts.lean#L231-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/PmModulusFacts.lean#L231-L245

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

theorem Formalism.RankGapBounds.LocalQuadraticParts.pm_modulus_facts (e J : ℕ) (hJ : 1 ≤ J) :
    2 ≤ 2 ^ (e + 2 - min e (Nat.log 2 J)) ∧ 2 ^ (e + 2 - min e (Nat.log 2 J)) ≤ 2 ^ (e + 2) ∧
      2 ^ e ≤ J * 2 ^ (e + 2 - min e (Nat.log 2 J)) := by sorry
