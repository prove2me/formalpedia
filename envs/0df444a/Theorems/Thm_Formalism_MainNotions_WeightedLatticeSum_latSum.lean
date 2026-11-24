-- Prove2me | Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_latSum
-- name    : Formalism.MainNotions.WeightedLatticeSum.latSum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:12:11.284138+00:00
-- url     : https://prove2.me/theorems/d0cd76d6-a841-4bf3-85dd-282b821c4c79
-- title:
--   Weighted Lattice Sum: lat Sum
-- statement:
--   The Weighted Lattice Sum construction uses the lat Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L222-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/WeightedLatticeSum.lean#L222-L299

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

theorem Formalism.MainNotions.WeightedLatticeSum.latSum (ι : Type) [Fintype ι] (P : Finset (ι → ℂ)) (R : ℝ) (hR : 1 ≤ R)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 1 ≤ ∏ i, ‖p i - q i‖) :
    ∑ p ∈ P, ∏ i, (max 1 (‖p i‖ / R)) ^ (-(3 : ℝ)) ≤ (64 * R) ^ (2 * Fintype.card ι) := by sorry
