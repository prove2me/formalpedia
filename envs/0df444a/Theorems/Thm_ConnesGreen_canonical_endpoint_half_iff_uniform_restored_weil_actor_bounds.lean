-- Prove2me | Theorems.Thm_ConnesGreen_canonical_endpoint_half_iff_uniform_restored_weil_actor_bounds
-- name    : ConnesGreen.canonical_endpoint_half_iff_uniform_restored_weil_actor_bounds
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T03:09:12.849026+00:00
-- url     : https://prove2.me/theorems/3c592141-cfa6-4166-864c-7d6981e3df4f
-- title:
--   Ordered endpoint half-bound iff uniform full-background Weil actor inequalities
-- statement:
--   For every c≥0 and finite selected packet S of actual nontrivial zeta zeros, the original ordered support-right marker has lower bound (1/2)I if and only if for every 0<η<1/2 there exists δ>0 such that for all positive windows c<T<c+δ and every original smooth test supported strictly in that window, ||M_S* x_g||² ≤ ((1/2−η)⁻¹−1)(Re W(g*starInv(g)) + ||M_S* x_g||² + ||B_S* x_g||²). The neighborhood is chosen before the window and test. The complete unselected-negative background B_S, actual zeros, multiplicities, reflection normalization and original physical carrier remain. The prescribed limits are positive regularization to zero followed by support approaching c from the right; no order is exchanged. The criterion includes c=0 and empty S and makes no finite-off-axis assumption. It does not identify the intended critical endpoint, establish its arithmetic bound, prove physical neutral-shell control, or prove RH.
-- source:
--   Recovered existing native theorem ConnesGreen.canonical_endpoint_half_iff_uniform_restored_weil_actor_bounds in WeilDefect/Connes/CanonicalGreenFiniteOffline.lean; exact source SHA256 6635c0780ee9b7093b2840fa883cc79d1722791702f89bbe6fb0472ab6b1b04a. Native signature and complete proof assembly audited; platform API adapters only. Original RPB108 form attachments remain a separate future formalization task.

import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
import Definitions.Def_WeilMarker_regularized_cost
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_endpoint_half_iff_uniform_restored_weil_actor_bounds
    (c : ℝ) (hc : 0 ≤ c) (S : Finset CriticalZeros) :
    (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc S ↔
    ∀ η : ℝ, 0 < η → η < 1 / 2 → ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + δ →
        ∀ g : ℝ → ℂ, SupportedTest T g →
          ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 ≤
          ((1 / 2 - η)⁻¹ - 1) * ((weilDistribution (conv g (starInv g))).re +
            ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 +
            ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2) := by sorry
