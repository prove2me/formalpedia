-- Prove2me | Theorems.Thm_ConnesGreen_actual_zero_half_bound_iff_finite_restoration
-- name    : ConnesGreen.actual_zero_half_bound_iff_finite_restoration
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T05:29:51.317446+00:00
-- url     : https://prove2.me/theorems/43def632-b512-4812-924b-23db4d2f4e26
-- title:
--   Exact arithmetic half-bound obstruction after actual-zero finite marker restoration
-- statement:
--   Fix a positive support window $t$ and finite packet $\Pi$ of actual nontrivial zeta zeros. There are fixed bounded syntheses $P,M$ of the original all-positive actors and selected negative actors, with their exact original basis columns. Put $L=PP^*$. At every $\varepsilon>0$, the full selected marker satisfies
--   $$\Gamma(L+\varepsilon I,M)\ge\tfrac12I$$
--   if and only if, for every $0<\alpha<1$, there is a finite actual-zero restoration packet $F\supseteq\Pi$ whose complete complementary negative synthesis $B_F$ has exactly its original basis columns and satisfies
--   $$\|B_FB_F^*\|\le\alpha\varepsilon,\qquad
--   \Gamma(L+\varepsilon I-B_FB_F^*,M)\ge(\tfrac12-\alpha)I.$$
--   The support window, regularization scale, selected compression, analytic multiplicities and pair normalization remain the same on both sides. Exact columns determine these bounded operators uniquely through the existing synthesis custody theorem.
--
--   This equivalence localizes the remaining arithmetic lower bound after the complete infinite tail has been controlled at the correct relative scale. It proves neither side unconditionally. In particular, it does not supply the finite-restored half-bound, exchange endpoint limits, establish neutral-shell persistence, or prove RH.
-- source:
--   monocap-tech/weil, WeilDefect/Screening/ShortedCovariance.lean (operatorInverse), WeilDefect/Screening/MarkerStability.lean (selectedCost, marker), and provenance/rh/checkpoints/RH_ZERO_PROV_4_INFINITE_NBR_DIAGONAL_MARKER_STABILITY_20260920.md, equations (3)-(8). Native base commit b019d40205680f9761a4b0a80cbcad56ee1b606b; exact new source is in Connes_Weil_Green_Marker_Recovery.zip. Native exact instantiation: WeilDefect/Connes/CanonicalGreenMarker.lean, actual_zero_diagonal_marker_recovery. Exact obstruction exports: canonical_regularized_half_bound_iff_finite_restoration and actual_zero_half_bound_iff_finite_restoration.

import Definitions.Def_ConnesGreen_actual_pair_columns
import Definitions.Def_WeilMarker_regularized_cost
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder

theorem ConnesGreen.actual_zero_half_bound_iff_finite_restoration (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ∃ P : ℓ²(CriticalZeros, ℂ) →L[ℂ] Physical t,
    ∃ M : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] Physical t,
      (∀ ρ, P (lp.single 2 ρ (1 : ℂ)) =
        positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) ∧
      (∀ ρ, M (lp.single 2 ρ (1 : ℂ)) =
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
      (∀ ε : ℝ, 0 < ε →
        ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
          ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ marker (P ∘L P.adjoint + ε • 1) M ↔
        ∀ α : ℝ, 0 < α → α < 1 →
          ∃ F : Finset CriticalZeros, S ⊆ F ∧
          ∃ B : ℓ²({ρ : CriticalZeros // ρ ∉ F}, ℂ) →L[ℂ] Physical t,
            (∀ ρ, B (lp.single 2 ρ (1 : ℂ)) =
              negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
            ‖B ∘L B.adjoint‖ ≤ α * ε ∧
            (1 / 2 - α) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
              ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤
              marker (P ∘L P.adjoint + ε • 1 - B ∘L B.adjoint) M)) := by sorry
