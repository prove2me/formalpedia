-- Prove2me | Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_tele
-- name    : Formalism.MainNotions.WeightedLatticeSum.tele
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:12:17.751981+00:00
-- url     : https://prove2.me/theorems/f35bdb5e-9778-422e-9acc-226e93edb053
-- title:
--   Weighted Lattice Sum: tele
-- statement:
--   The Weighted Lattice Sum construction uses the tele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L40-L45

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

theorem Formalism.MainNotions.WeightedLatticeSum.tele (k : ℝ) (hk : 2 ≤ k) :
    1 / (k * Real.sqrt k) ≤ 2 * (1 / Real.sqrt (k - 1) - 1 / Real.sqrt k) := by sorry
