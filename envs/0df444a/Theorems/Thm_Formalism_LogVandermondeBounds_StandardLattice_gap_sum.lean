-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_gap_sum
-- name    : Formalism.LogVandermondeBounds.StandardLattice.gap_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:52:35.81919+00:00
-- url     : https://prove2.me/theorems/8bd57551-18c5-4eb9-adf5-da0370467b6f
-- title:
--   Standard Lattice: gap sum
-- statement:
--   The Standard Lattice construction uses the gap sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogVandermondeVariationUnbounded.lean#L46-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogVandermondeVariationUnbounded.lean#L46-L62

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogVandermondeVariationUnbounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset

theorem Formalism.LogVandermondeBounds.StandardLattice.gap_sum {n : ℕ} (u : Fin (n + 2) → ℝ) (g : ℝ)
    (h : ∀ i j : Fin (n + 2), 1 ≤ i.val → j.val = i.val + 1 → j.val ≤ n → g ≤ u i - u j)
    (a : Fin (n + 2)) (ha : 1 ≤ a.val) :
    ∀ m : ℕ, ∀ b : Fin (n + 2), b.val = a.val + m → b.val ≤ n → g * m ≤ u a - u b := by sorry
