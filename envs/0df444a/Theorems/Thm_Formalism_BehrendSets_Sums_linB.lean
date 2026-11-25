-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Sums_linB
-- name    : Formalism.BehrendSets.Sums.linB
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:20:15.652653+00:00
-- url     : https://prove2.me/theorems/110349f0-ba17-4b9c-aca4-e07ff90aebb2
-- title:
--   Sums: lin B
-- statement:
--   The Sums construction uses the lin B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/TwoLeCastOfTwoLe.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/TwoLeCastOfTwoLe.lean#L36-L39

import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_TwoLeCastOfTwoLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Real
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Sums

theorem Formalism.BehrendSets.Sums.linB (M k : ℕ) (L : ℝ) (hM : 2 ≤ M) (hL : 0 ≤ L) :
    L / (((M * (k + 1) - 1 : ℕ)) : ℝ) ≤ 2 * L * (1 / ((k : ℝ) + 1)) / (M : ℝ) := by sorry
