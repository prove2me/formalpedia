-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_place_bound
-- name    : Formalism.LogVandermondeBounds.StandardLattice.place_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:42:53.131085+00:00
-- url     : https://prove2.me/theorems/2e494d74-b8f8-4b76-a671-d2d30d77676f
-- title:
--   Standard Lattice: place bound
-- statement:
--   The Standard Lattice construction uses the place bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogRatioLowerBoundOfLogVandermondeGap.lean#L53-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogRatioLowerBoundOfLogVandermondeGap.lean#L53-L160

import Definitions.Def_Formalism_LogVandermondeBounds_VandPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogRatioLowerBoundOfLogVandermondeGap
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

theorem Formalism.LogVandermondeBounds.StandardLattice.place_bound (hV : VandPlace) (ε x C₀ : ℝ) (hε : 0 < ε) (hx : 1 ≤ x) (hC₀ : 0 ≤ C₀)
    (k m : ℕ) (Δ : ℝ) (u v b w : ℕ → ℝ) (hk : 2 ≤ k) (hm : 1 ≤ m) (hΔ : 1 ≤ Δ)
    (hkx : (k : ℝ) ≤ x ^ C₀)
    (hP : PlaceData x Δ (x * Real.exp (x ^ ε)) (Real.exp (x ^ ε)) k m u v b w) :
    0 < vandN u k ∧ 0 < vandN (rowPar k v b) (k - 1 + m) ∧ (∀ j, j < m → 0 < w j) ∧
    (k : ℝ) * ∑ j ∈ range m, Real.log (w j)
      ≤ (Real.log (vandN (rowPar k v b) (k - 1 + m)) - Real.log (vandN u k))
        + k * x ^ ε * (20 + (2 + 2 * C₀) / ε) + 2 * m * x ^ ε := by sorry
