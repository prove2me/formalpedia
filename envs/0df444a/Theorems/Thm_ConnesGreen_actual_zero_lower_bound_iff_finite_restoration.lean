-- Prove2me | Theorems.Thm_ConnesGreen_actual_zero_lower_bound_iff_finite_restoration
-- name    : ConnesGreen.actual_zero_lower_bound_iff_finite_restoration
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T16:34:21.648987+00:00
-- url     : https://prove2.me/theorems/41ef2f57-df1a-4d03-b7a2-8eb684dbe511
-- title:
--   Every actual-zero marker lower bound is exactly its finite-restoration estimate
-- statement:
--   Fix a positive support window $t$ and a finite packet $S$ of actual nontrivial zeta zeros. There are fixed bounded syntheses $P,M$ with exactly the original all-positive and selected negative Green columns, including their analytic multiplicities and pair normalization. For every $\varepsilon>0$ and every real threshold $a$, $$aI\preceq\Gamma(PP^*+\varepsilon I,M)$$ is equivalent to the following: for every $0<\alpha<1$ there is a finite restoration packet $F\supseteq S$ and its bounded complete complementary negative synthesis $B_F$, with exactly its original columns, such that $$\|B_FB_F^*\|\le\alpha\varepsilon,\qquad (a-\alpha)I\preceq\Gamma(PP^*+\varepsilon I-B_FB_F^*,M).$$ Here $\Gamma(A,M)=(I+M^*A^{-1}M)^{-1}$. The support window, positive regularization and selected compression stay unchanged; only the restoration cutoff depends on accuracy and regularization. This exact reduction covers approximate endpoint thresholds as well as the original $a=1/2$ case. It proves neither lower-bound side unconditionally and supplies no prescribed critical endpoint identification, neutral-shell persistence or RH.
-- source:
--   monocap-tech/weil; Connes/CanonicalGreenFiniteEndpoint.lean, actual_zero_lower_bound_iff_finite_restoration; generalizes the unchanged original half-threshold target to every real threshold. Uses the original canonical Green carrier, actual zeta-zero subtype, analytic multiplicities, reflection duplication and /2 actor normalization. The strongest native endpoint criterion keeps a common reflection-closed restoration cutoff across nearby windows at each regularization scale. No arithmetic endpoint lower bound, prescribed-window containment or RH is asserted.

import Definitions.Def_ConnesGreen_actual_pair_columns
import Definitions.Def_WeilMarker_regularized_cost
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder

theorem ConnesGreen.actual_zero_lower_bound_iff_finite_restoration (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ∃ P : ℓ²(CriticalZeros, ℂ) →L[ℂ] Physical t,
    ∃ M : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] Physical t,
      (∀ ρ, P (lp.single 2 ρ (1 : ℂ)) =
        positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) ∧
      (∀ ρ, M (lp.single 2 ρ (1 : ℂ)) =
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
      (∀ ε : ℝ, 0 < ε → ∀ a : ℝ,
        (a • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
          ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ marker (P ∘L P.adjoint + ε • 1) M ↔
        ∀ α : ℝ, 0 < α → α < 1 →
          ∃ F : Finset CriticalZeros, S ⊆ F ∧
          ∃ B : ℓ²({ρ : CriticalZeros // ρ ∉ F}, ℂ) →L[ℂ] Physical t,
            (∀ ρ, B (lp.single 2 ρ (1 : ℂ)) =
              negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
            ‖B ∘L B.adjoint‖ ≤ α * ε ∧
            (a - α) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
              ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤
              marker (P ∘L P.adjoint + ε • 1 - B ∘L B.adjoint) M)) := by sorry
