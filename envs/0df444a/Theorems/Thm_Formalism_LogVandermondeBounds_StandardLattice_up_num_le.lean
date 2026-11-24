-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_up_num_le
-- name    : Formalism.LogVandermondeBounds.StandardLattice.up_num_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:20.877363+00:00
-- url     : https://prove2.me/theorems/13cea66f-a71e-4998-b632-216ff026ce90
-- title:
--   Standard Lattice: up num le
-- statement:
--   The Standard Lattice construction uses the up num le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/UpperPlaceHolds.lean#L116-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/UpperPlaceHolds.lean#L116-L209

import Definitions.Def_Formalism_LogVandermondeBounds_UpperPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_UpperPlaceHolds
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

theorem Formalism.LogVandermondeBounds.StandardLattice.up_num_le (n m : ℕ) (lam v : ℕ → ℝ) (Bd : ℝ) (hBd : 1 ≤ Bd)
    (hlamv : ∀ i, i < n + 1 → lam i = v i)
    (hpos : ∀ a c, a < c → c < n + 1 + m → 0 < lam a - lam c + (nBetween (n + 2) a c : ℝ))
    (hle : ∀ a c, a < c → c < n + 1 + m → lam a - lam c + (nBetween (n + 2) a c : ℝ) ≤ Bd) :
    ∏ a ∈ range (n + 1 + m), ∏ c ∈ (Ico (a + 1) (n + 1 + m)).filter
        (fun c => plusSign (n + 2) c = plusSign (n + 2) a),
        (lam a - lam c + (nBetween (n + 2) a c : ℝ))
      ≤ vandN v (n + 1) * Bd ^ (m * (n + 1 + m)) := by sorry
