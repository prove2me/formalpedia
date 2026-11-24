-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_pm_resid
-- name    : Formalism.RankGapBounds.LocalQuadraticParts.pm_resid
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:26:11.374578+00:00
-- url     : https://prove2.me/theorems/7e126c7f-845a-427a-8a61-4af1904748d6
-- title:
--   Local Quadratic Parts: pm resid
-- statement:
--   The Local Quadratic Parts construction uses the pm resid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/PmModulusFacts.lean#L116-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/PmModulusFacts.lean#L116-L134

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

theorem Formalism.RankGapBounds.LocalQuadraticParts.pm_resid (hI : OrdersIff) (e J l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)) (hodd : l % 2 = 1)
    (hord : orderOf (hOf e l hl) ≤ J) :
    (l : ZMod (2 ^ (e + 2 - min e (Nat.log 2 J)))) = 1 ∨
      (l : ZMod (2 ^ (e + 2 - min e (Nat.log 2 J)))) = -1 := by sorry
