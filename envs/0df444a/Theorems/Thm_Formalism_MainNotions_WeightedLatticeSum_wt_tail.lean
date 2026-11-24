-- Prove2me | Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_wt_tail
-- name    : Formalism.MainNotions.WeightedLatticeSum.wt_tail
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:11:54.188005+00:00
-- url     : https://prove2.me/theorems/beb10463-297e-40a5-af32-0a4f60f05896
-- title:
--   Weighted Lattice Sum: wt tail
-- statement:
--   The Weighted Lattice Sum construction uses the wt tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L64-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L64-L75

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

theorem Formalism.MainNotions.WeightedLatticeSum.wt_tail (R : ℝ) (hR : 1 ≤ R) (N : ℕ) (hN : 2 * R ≤ N) (j : ℕ) :
    wt R (N + 2 + j) ≤ 2 * (2 * R) * Real.sqrt (2 * R) *
      (1 / Real.sqrt ((N : ℝ) + (j : ℝ)) - 1 / Real.sqrt ((N : ℝ) + ((j + 1 : ℕ) : ℝ))) := by sorry
