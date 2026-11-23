-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Sums_two_le_cast_of_two_le
-- name    : Formalism.BehrendSets.Sums.two_le_cast_of_two_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:07.028402+00:00
-- url     : https://prove2.me/theorems/c4d6b2ef-8603-461b-8927-ee0fa40b2d96
-- title:
--   Sums: two le cast of two le
-- statement:
--   The Sums construction uses the two le cast of two le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/TwoLeCastOfTwoLe.lean#L34-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/TwoLeCastOfTwoLe.lean#L34-L34

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

theorem Formalism.BehrendSets.Sums.two_le_cast_of_two_le (M : ℕ) (hM : 2 ≤ M) : (2 : ℝ) ≤ (M : ℝ) := by sorry
