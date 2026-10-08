-- Prove2me | Theorems.Thm_ConnesGreen_actual_zero_diagonal_marker_recovery
-- name    : ConnesGreen.actual_zero_diagonal_marker_recovery
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T05:25:39.17632+00:00
-- url     : https://prove2.me/theorems/bba58397-dd5d-4948-93db-4242fd825ef1
-- title:
--   Finite restoration of the complete actual-zero background at every marker regularization scale
-- statement:
--   Fix a positive support window $t$ and finite selected packet $\Pi$ of actual nontrivial zeta zeros. On the previously certified canonical Green carrier there are bounded synthesis operators $P$ and $M$ whose basis columns are exactly all original positive pair actors and the original negative actors in $\Pi$, respectively. These fixed operators satisfy the following for every $\varepsilon>0$ and every $0<\alpha<1$: there is a finite actual-zero packet $F\supseteq\Pi$ and a bounded synthesis $B_F$ containing exactly every original negative actor outside $F$ such that, with $L=PP^*$ and $R_F=B_FB_F^*$,
--   $$\|R_F\|\le\alpha\varepsilon,\qquad L+\varepsilon I-R_F\text{ is strictly positive},$$
--   $$0\le\Gamma(L+\varepsilon I,M)-\Gamma(L+\varepsilon I-R_F,M),$$
--   $$\|\Gamma(L+\varepsilon I,M)-\Gamma(L+\varepsilon I-R_F,M)\|\le\alpha.$$
--   The carrier, analytic multiplicities, reflection duplication, pair normalization, support window and selected compression remain unchanged. All unselected zeros are included in the covariance tail before finite restoration; no abstract zero surrogate is introduced.
--
--   The cutoff may depend on $t,\Pi,\varepsilon,\alpha$. This proves finite recovery at each regularization scale and remains valid when the selected inverse cost is large. It does not claim one fixed finite cutoff for all scales, uniformity over moving support windows, an explicit ordinate-cutoff rate, a marker half-threshold bound, or RH.
-- source:
--   monocap-tech/weil, WeilDefect/Screening/ShortedCovariance.lean (operatorInverse), WeilDefect/Screening/MarkerStability.lean (selectedCost, marker), and provenance/rh/checkpoints/RH_ZERO_PROV_4_INFINITE_NBR_DIAGONAL_MARKER_STABILITY_20260920.md, equations (3)-(8). Native base commit b019d40205680f9761a4b0a80cbcad56ee1b606b; exact new source is in Connes_Weil_Green_Marker_Recovery.zip. Native exact instantiation: WeilDefect/Connes/CanonicalGreenMarker.lean, actual_zero_diagonal_marker_recovery.

import Definitions.Def_ConnesGreen_actual_pair_columns
import Definitions.Def_WeilMarker_regularized_cost
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder

theorem ConnesGreen.actual_zero_diagonal_marker_recovery (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ∃ P : ℓ²(CriticalZeros, ℂ) →L[ℂ] Physical t,
    ∃ M : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] Physical t,
      (∀ ρ, P (lp.single 2 ρ (1 : ℂ)) =
        positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) ∧
      (∀ ρ, M (lp.single 2 ρ (1 : ℂ)) =
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
      (∀ ε : ℝ, 0 < ε → ∀ α : ℝ, 0 < α → α < 1 →
        ∃ F : Finset CriticalZeros, S ⊆ F ∧
        ∃ B : ℓ²({ρ : CriticalZeros // ρ ∉ F}, ℂ) →L[ℂ] Physical t,
          (∀ ρ, B (lp.single 2 ρ (1 : ℂ)) =
            negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
          ‖B ∘L B.adjoint‖ ≤ α * ε ∧
          IsStrictlyPositive (P ∘L P.adjoint + ε • 1 - B ∘L B.adjoint) ∧
          0 ≤ marker (P ∘L P.adjoint + ε • 1) M -
            marker (P ∘L P.adjoint + ε • 1 - B ∘L B.adjoint) M ∧
          ‖marker (P ∘L P.adjoint + ε • 1) M -
            marker (P ∘L P.adjoint + ε • 1 - B ∘L B.adjoint) M‖ ≤ α) := by sorry
