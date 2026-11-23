-- Prove2me | Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_rpow_neg_three_halves
-- name    : Formalism.MainNotions.WeightedLatticeSum.rpow_neg_three_halves
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:32.611047+00:00
-- url     : https://prove2.me/theorems/d9ac39c8-101b-4087-ac12-a0b20bc22485
-- title:
--   Weighted Lattice Sum: rpow neg three halves
-- statement:
--   The Weighted Lattice Sum construction uses the rpow neg three halves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L11-L13

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

theorem Formalism.MainNotions.WeightedLatticeSum.rpow_neg_three_halves {t : ℝ} (ht : 0 < t) : t ^ (-(3 / 2 : ℝ)) = 1 / (t * Real.sqrt t) := by sorry
