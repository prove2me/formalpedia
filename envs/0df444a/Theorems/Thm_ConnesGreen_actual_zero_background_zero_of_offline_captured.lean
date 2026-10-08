-- Prove2me | Theorems.Thm_ConnesGreen_actual_zero_background_zero_of_offline_captured
-- name    : ConnesGreen.actual_zero_background_zero_of_offline_captured
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T17:45:13.643062+00:00
-- url     : https://prove2.me/theorems/eb26b7cc-b76c-413d-9897-6c5b5c57c5d8
-- title:
--   Capturing all actual off-line zeros annihilates the original negative background
-- statement:
--   Fix the original positive support window $t$ and a finite packet $F$ of actual nontrivial zeta zeros. Assume that every actual zero with real part different from $1/2$ belongs to $F$. Then the complete original negative synthesis on the complement of $F$ is the zero bounded operator, with exactly the original multiplicity-weighted reflected-pair basis columns. The remaining critical-line negative columns vanish because reflection fixes their zero; their positive channels and multiplicities are retained. This is an exact conditional background result, not an arithmetic positivity bound or RH theorem.
-- source:
--   monocap-tech/weil, CanonicalGreenFiniteOffline.lean. Uses the original actual-zeta subtype, analytic multiplicities, reflected pair columns, physical carrier and /2 normalization. A finite packet capturing every off-line zero is an explicit conditional finite-branch hypothesis, not RH and not a prescribed-packet identification. No arithmetic lower estimate or RH asserted.

import Definitions.Def_ConnesGreen_actual_pair_columns
import Definitions.Def_WeilMarker_regularized_cost
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder

theorem ConnesGreen.actual_zero_background_zero_of_offline_captured
    (t : ℝ) (ht : 0 < t) (F : Finset CriticalZeros)
    (hF : ∀ ρ : CriticalZeros, ρ.1.re ≠ 1 / 2 → ρ ∈ F) :
    ∃ B : ℓ²({ρ : CriticalZeros // ρ ∉ F}, ℂ) →L[ℂ] Physical t,
      (∀ ρ, B (lp.single 2 ρ (1 : ℂ)) =
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧ B = 0 := by sorry
