-- Prove2me | Theorems.Thm_ConnesGreen_actual_zero_uniform_marker_recovery
-- name    : ConnesGreen.actual_zero_uniform_marker_recovery
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T05:42:44.11942+00:00
-- url     : https://prove2.me/theorems/5a8abd14-aa3c-4b98-a78a-0d2ab852fda1
-- title:
--   One reflection-closed actual-zero cutoff gives marker recovery uniformly over support windows
-- statement:
--   Let $T$ be an upper support bound and $\Pi$ a fixed finite packet of actual nontrivial zeta zeros. For every $\varepsilon>0$ and $0<\alpha<1$, there exists one finite actual-zero packet $F\supseteq\Pi$, closed under $\rho\mapsto1-\overline\rho$, that works for every support window $0<t\le T$. On each original canonical Green carrier $H_t$, bounded operators $P_t,M_t,B_{F,t}$ have exactly the original full-positive, selected negative, and complete complementary negative basis columns. With $L_t=P_tP_t^*$ and $R_{F,t}=B_{F,t}B_{F,t}^*$ they satisfy
--   $$\|R_{F,t}\|\le\alpha\varepsilon,\qquad L_t+\varepsilon I-R_{F,t}\text{ is strictly positive},$$
--   $$0\le\Gamma(L_t+\varepsilon I,M_t)-\Gamma(L_t+\varepsilon I-R_{F,t},M_t),$$
--   $$\|\Gamma(L_t+\varepsilon I,M_t)-\Gamma(L_t+\varepsilon I-R_{F,t},M_t)\|\le\alpha.$$
--   The finite cutoff is chosen before $t$ and is independent of the support window throughout this range. Exact original columns uniquely fix the bounded operators. All actual zeros, analytic multiplicities, reflection duplication, pair normalization and the selected packet are preserved.
--
--   This closes support-uniform finite recovery of the infinite negative background at each Picard regularization scale. The cutoff may depend on $T,\Pi,\varepsilon,\alpha$. The theorem supplies no cutoff independent of $\varepsilon$, explicit logarithmic ordinate-tail rate, arithmetic half-threshold bound, neutral-shell persistence, endpoint-limit interchange, or RH theorem.
-- source:
--   monocap-tech/weil, WeilDefect/Screening/ShortedCovariance.lean (operatorInverse), WeilDefect/Screening/MarkerStability.lean (selectedCost, marker), and provenance/rh/checkpoints/RH_ZERO_PROV_4_INFINITE_NBR_DIAGONAL_MARKER_STABILITY_20260920.md, equations (3)-(8). Native base commit b019d40205680f9761a4b0a80cbcad56ee1b606b; exact new source is in Connes_Weil_Green_Marker_Recovery.zip. Native exact instantiation: WeilDefect/Connes/CanonicalGreenMarker.lean, actual_zero_diagonal_marker_recovery. Uniform envelope and reflection-closed cutoff: WeilDefect/Connes/CanonicalGreenMarkerUniform.lean, actual_Green_energy_uniform_bound, canonical_uniform_small_tail, canonical_uniform_diagonal_marker_recovery, and actual_zero_uniform_marker_recovery. Original Dirichlet energy estimate: WeilDefect/DirichletResolvent.lean, problemOneColumnEnergySq_le.

import Definitions.Def_ConnesGreen_actual_pair_columns
import Definitions.Def_WeilMarker_regularized_cost
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder

theorem ConnesGreen.actual_zero_uniform_marker_recovery (T : ℝ) (S : Finset CriticalZeros) (ε α : ℝ)
    (hε : 0 < ε) (hα : 0 < α) (hα1 : α < 1) :
    ∃ F : Finset CriticalZeros, S ⊆ F ∧
      (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
      ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
      ∃ P : ℓ²(CriticalZeros, ℂ) →L[ℂ] Physical t,
      ∃ M : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] Physical t,
      ∃ B : ℓ²({ρ : CriticalZeros // ρ ∉ F}, ℂ) →L[ℂ] Physical t,
        (∀ ρ, P (lp.single 2 ρ (1 : ℂ)) =
          positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) ∧
        (∀ ρ, M (lp.single 2 ρ (1 : ℂ)) =
          negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
        (∀ ρ, B (lp.single 2 ρ (1 : ℂ)) =
          negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
        ‖B ∘L B.adjoint‖ ≤ α * ε ∧
        IsStrictlyPositive (P ∘L P.adjoint + ε • 1 - B ∘L B.adjoint) ∧
        0 ≤ marker (P ∘L P.adjoint + ε • 1) M -
          marker (P ∘L P.adjoint + ε • 1 - B ∘L B.adjoint) M ∧
        ‖marker (P ∘L P.adjoint + ε • 1) M -
          marker (P ∘L P.adjoint + ε • 1 - B ∘L B.adjoint) M‖ ≤ α := by sorry
