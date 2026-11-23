-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Sums_linB_real
-- name    : Formalism.BehrendSets.Sums.linB_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:06.433633+00:00
-- url     : https://prove2.me/theorems/314b46f7-f1e2-4c1b-8ebd-cd809170b834
-- title:
--   Sums: lin B real
-- statement:
--   The Sums construction uses the lin B real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/TwoLeCastOfTwoLe.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/TwoLeCastOfTwoLe.lean#L13-L21

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

theorem Formalism.BehrendSets.Sums.linB_real (m K L : ℝ) (hm : 2 ≤ m) (hK : 1 ≤ K) (hL : 0 ≤ L) :
    L / (m * K - 1) ≤ 2 * L * (1 / K) / m := by sorry
