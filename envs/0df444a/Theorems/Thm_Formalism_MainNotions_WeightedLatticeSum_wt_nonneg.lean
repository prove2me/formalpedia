-- Prove2me | Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_wt_nonneg
-- name    : Formalism.MainNotions.WeightedLatticeSum.wt_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:54:38.456803+00:00
-- url     : https://prove2.me/theorems/6f5cb10c-ed7c-4f09-a328-e50800450475
-- title:
--   Weighted Lattice Sum: wt nonneg
-- statement:
--   The Weighted Lattice Sum construction uses the wt nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L15-L17

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

theorem Formalism.MainNotions.WeightedLatticeSum.wt_nonneg (R : ℝ) (m : ℕ) : 0 ≤ wt R m := by sorry
