-- Prove2me | Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_sum_wt_le
-- name    : Formalism.MainNotions.WeightedLatticeSum.sum_wt_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:12:13.847389+00:00
-- url     : https://prove2.me/theorems/fa796aba-1a1b-4921-8699-fa36b5414164
-- title:
--   Weighted Lattice Sum: sum wt le
-- statement:
--   The Weighted Lattice Sum construction uses the sum wt le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L77-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L77-L114

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_WeightedLatticeSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.WeightedLatticeSum
open Finset

theorem Formalism.MainNotions.WeightedLatticeSum.sum_wt_le (R : ℝ) (hR : 1 ≤ R) (T : Finset ℕ) : ∑ m ∈ T, wt R m ≤ 9 * R := by sorry
