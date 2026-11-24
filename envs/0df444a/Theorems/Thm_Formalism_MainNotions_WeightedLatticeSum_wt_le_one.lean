-- Prove2me | Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_wt_le_one
-- name    : Formalism.MainNotions.WeightedLatticeSum.wt_le_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:12:04.235942+00:00
-- url     : https://prove2.me/theorems/65ef6991-c02c-4357-b0eb-b4b99b57f6af
-- title:
--   Weighted Lattice Sum: wt le one
-- statement:
--   The Weighted Lattice Sum construction uses the wt le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L19-L21

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

theorem Formalism.MainNotions.WeightedLatticeSum.wt_le_one (R : ℝ) (m : ℕ) : wt R m ≤ 1 := by sorry
