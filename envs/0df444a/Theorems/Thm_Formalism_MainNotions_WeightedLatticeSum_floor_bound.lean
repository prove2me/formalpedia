-- Prove2me | Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_floor_bound
-- name    : Formalism.MainNotions.WeightedLatticeSum.floor_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:12:20.978908+00:00
-- url     : https://prove2.me/theorems/d145afd3-3506-4221-bd98-2c65efa570d2
-- title:
--   Weighted Lattice Sum: floor bound
-- statement:
--   The Weighted Lattice Sum construction uses the floor bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L165-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L165-L175

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

theorem Formalism.MainNotions.WeightedLatticeSum.floor_bound (R : ℝ) (hR : 1 ≤ R) (x : ℝ) :
    (max 1 (|x| / R)) ^ (-(3 / 2 : ℝ)) ≤ wt R (⌊2 * x⌋).natAbs := by sorry
