-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_pair_bound
-- name    : Formalism.LogVandermondeBounds.StandardLattice.pair_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:00.485861+00:00
-- url     : https://prove2.me/theorems/d00e3f25-4b80-45c9-b258-32160441fcb7
-- title:
--   Standard Lattice: pair bound
-- statement:
--   The Standard Lattice construction uses the pair bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogVandermondeVariationUnbounded.lean#L108-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogVandermondeVariationUnbounded.lean#L108-L219

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

theorem Formalism.LogVandermondeBounds.StandardLattice.pair_bound {n : ℕ} {Δ : ℝ} {u u' : Fin (n + 2) → ℝ} (hw : WordPair n Δ u u')
    (a b : Fin (n + 2)) (hab : a < b) :
    |Real.log (u a - u b) - Real.log (u' a - u' b)| ≤
      2 / (((b.val - a.val - 1 : ℕ) : ℝ) + 1) +
      ((if a = 0 ∧ b = ⟨1, by omega⟩ then Real.log (1 + Δ) else 0) +
       (if a = ⟨n, by omega⟩ ∧ b = Fin.last (n + 1) then Real.log (1 + Δ) else 0)) := by sorry
