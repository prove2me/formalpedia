-- Prove2me | Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_norm_lt_one_of_cell
-- name    : Formalism.MainNotions.WeightedLatticeSum.norm_lt_one_of_cell
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:12:09.300651+00:00
-- url     : https://prove2.me/theorems/b0b88d8a-95c4-41b9-bc22-9b7dc06732b3
-- title:
--   Weighted Lattice Sum: norm lt one of cell
-- statement:
--   The Weighted Lattice Sum construction uses the norm lt one of cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L201-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L201-L220

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

theorem Formalism.MainNotions.WeightedLatticeSum.norm_lt_one_of_cell (z w : ℂ) (h1 : ⌊2 * z.re⌋ = ⌊2 * w.re⌋) (h2 : ⌊2 * z.im⌋ = ⌊2 * w.im⌋) :
    ‖z - w‖ < 1 := by sorry
