-- Prove2me | Theorems.Thm_ConnesGreen_canonicalPicardMarker_lower_iff_restored_weil_actor_bound
-- name    : ConnesGreen.canonicalPicardMarker_lower_iff_restored_weil_actor_bound
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T03:02:27.186508+00:00
-- url     : https://prove2.me/theorems/174c69ca-67ee-4b12-a9e5-1d268efd3e14
-- title:
--   Original Picard marker bound iff full-background restored Weil actor inequality
-- statement:
--   For every positive support window t, every finite selected packet S of actual nontrivial zeta zeros, and every 0<β<1, the original Picard marker has lower bound βI if and only if every original smooth test supported strictly in the window obeys ||M_S* x_g||² ≤ (β⁻¹−1)(Re W(g*starInv(g)) + ||M_S* x_g||² + ||B_S* x_g||²). Here x_g is the original physical-carrier embedding of Lg, M_S is the selected actual-negative-column synthesis, and B_S retains the entire negative complement outside S. Multiplicities and reflected normalization are unchanged. This is an exact characterization, not a proof of the arithmetic inequality. Empty packets are included. There is no finiteness assumption on off-axis zeros and no regularization or finite restoration cutoff in the criterion.
-- source:
--   Recovered existing native theorem ConnesGreen.canonicalPicardMarker_lower_iff_restored_weil_actor_bound in WeilDefect/Connes/CanonicalGreenFiniteOffline.lean; exact source SHA256 6635c0780ee9b7093b2840fa883cc79d1722791702f89bbe6fb0472ab6b1b04a. Native signature and complete proof assembly audited; platform API adapters only. Original RPB108 form attachments remain a separate future formalization task.

import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
import Definitions.Def_WeilMarker_regularized_cost
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonicalPicardMarker_lower_iff_restored_weil_actor_bound
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    β • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S ↔
    ∀ g : ℝ → ℂ, SupportedTest t g →
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 ≤
      (β⁻¹ - 1) * ((weilDistribution (conv g (starInv g))).re +
        ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 +
        ‖(canonicalBackgroundSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2) := by sorry
