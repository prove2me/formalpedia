-- Prove2me | Theorems.Thm_ConnesGreen_canonical_endpoint_half_iff_uniform_eventual_arithmetic
-- name    : ConnesGreen.canonical_endpoint_half_iff_uniform_eventual_arithmetic
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T18:56:03.344281+00:00
-- url     : https://prove2.me/theorems/3ea2a5ed-2422-43e6-8338-3f653ae70d2d
-- title:
--   Original endpoint half-bound is equivalent to uniform eventual restored arithmetic control
-- statement:
--   # Uniform eventual arithmetic control
--
--   For every T>0, fixed finite actual-zero selected packet S, finite requests K_n, and explicit positive vanishing schedules μ_n and ε_n with ε_n<1, there exists a nested reflection-closed restoration sequence F_n containing S and K_n. Every preceding tail estimate, ordered limit, and window-dependent eventual arithmetic equivalence is retained for that same F.
--
--   For each 0≤c<T, the original endpoint half-bound is equivalent to the following stronger condition: for every 0<η<1/2 there exist d>0 and N∈ℕ, with c+d≤T, such that for every n≥N, every c<t<c+d and every original SupportedTest t g,
--
--   $$
--   E_{S,t}(g)\le ((1/2-\eta)^{-1}-1)\bigl(\operatorname{Re}W(g*g^*)+E_{F_n,t}(g)+\mu_n D(g)\bigr).
--   $$
--
--   Here E_(A,t)(g)=‖N_(t,A)* sourceEmbed(t,problemOneL(g))‖² uses the original negative actual-zero synthesis and D(g)=∫‖g′‖²+(1/4)∫‖g‖². The coefficient multiplies the entire parenthesis. S remains the selected actor and F_n the restoration actor. No normalization of g is assumed in this arithmetic condition.
--
--   The cutoff N precedes the support window t and the test g. It is common to all nearby windows, all original supported tests, and all later n. The conditional common lower bound does not assert common-stage norm approximation to the endpoint, a joint norm limit, or any limit exchange. Neither the endpoint half-bound nor the arithmetic inequality is established unconditionally. RH remains open.
-- source:
--   # Common cutoff stage before nearby windows
--
--   For every T>0, fixed finite actual-zero selected packet S, finite requests K_n, and explicit positive vanishing schedules μ_n and ε_n with ε_n<1, there exists a nested reflection-closed restoration sequence F_n containing S and K_n. Every preceding tail estimate, ordered limit, and window-dependent eventual arithmetic equivalence is retained for that same F.
--
--   For each 0≤c<T, the original endpoint half-bound is equivalent to the following stronger condition: for every 0<η<1/2 there exist d>0 and N∈ℕ, with c+d≤T, such that for every n≥N, every c<t<c+d and every original SupportedTest t g,
--
--   $$
--   E_{S,t}(g)\le ((1/2-\eta)^{-1}-1)\bigl(\operatorname{Re}W(g*g^*)+E_{F_n,t}(g)+\mu_n D(g)\bigr).
--   $$
--
--   Here E_(A,t)(g)=‖N_(t,A)* sourceEmbed(t,problemOneL(g))‖² uses the original negative actual-zero synthesis and D(g)=∫‖g′‖²+(1/4)∫‖g‖². The coefficient multiplies the entire parenthesis. S remains the selected actor and F_n the restoration actor. No normalization of g is assumed in this arithmetic condition.
--
--   The cutoff N precedes the support window t and the test g. It is common to all nearby windows, all original supported tests, and all later n. The conditional common lower bound does not assert common-stage norm approximation to the endpoint, a joint norm limit, or any limit exchange. Neither the endpoint half-bound nor the arithmetic inequality is established unconditionally. RH remains open.
--
--   Assume the original endpoint half-bound. Apply the original support-right norm limit with tolerance η/2 and restrict its positive support radius to T−c. Every Picard marker in that interval then has scalar lower bound 1/2−η/2, by the self-adjoint norm perturbation estimate.
--
--   The original Picard marker is a lower bound for every positive regularized marker, by its greatest-lower-bound specification. In particular, this comparison holds at μ_n for all n. Since ε_n→0, choose a single N such that ε_n<η/2 for every n≥N. This choice precedes t. The inherited restored-marker error is at most ε_n uniformly over every 0<t≤T, so every restored marker at a nearby support and n≥N has scalar lower bound 1/2−η. Its self-adjointness follows from the inherited strict-positive restored covariance. Original regularized self-adjointness also follows from its order comparison to the nonnegative Picard marker.
--
--   Apply the accepted finite-marker arithmetic bridge with β=1/2−η and regularization μ_n. This gives the exact arithmetic inequality for every original supported test with the same N for all nearby windows.
--
--   Conversely, the common-stage condition implies the preceding window-dependent condition by choosing the same N at each t. The accepted preceding equivalence then gives the original endpoint half-bound. All preceding witness properties are retained unchanged.
--
--   Native certification uses the closed preceding assembly over pinned certified modules. Platform certification imports the accepted preceding arithmetic equivalence and the finite-marker arithmetic bridge. No new definition, axiom, assumed arithmetic positivity, selected actor, or repository source change is introduced.

import Definitions.Def_ConnesGreen_RG0_original_actors
import Definitions.Def_WeilMarker_regularized_cost
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_endpoint_half_iff_uniform_eventual_arithmetic
    (T : ℝ) (hT : 0 < T) (S : Finset CriticalZeros)
    (K : ℕ → Finset CriticalZeros) (μ ε : ℕ → ℝ)
    (hμ : ∀ n, 0 < μ n) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n < 1)
    (hμlim : Tendsto μ atTop (nhds 0)) (hεlim : Tendsto ε atTop (nhds 0)) :
    ∃ F : ℕ → Finset CriticalZeros, Monotone F ∧
      (∀ n, S ⊆ F n ∧ K n ⊆ F n ∧ (∀ τ ∈ F n, reflectedZero τ ∈ F n)) ∧
      (∀ n, ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∃ Ptail : ℓ²({τ : CriticalZeros // τ ∉ (F n)}, ℂ) →L[ℂ] Physical t,
          (∀ τ, Ptail (lp.single 2 τ (1 : ℂ)) =
            positiveGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ.1) ∧
          ‖Ptail ∘L Ptail.adjoint‖ + ‖canonicalTailCovariance t ht (F n)‖ < ε n ∧
          (∀ ν : ℝ, μ n ≤ ν →
            ‖canonicalTailCovariance t ht (F n)‖ ≤ ε n * ν ∧
            IsStrictlyPositive (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n)) ∧
            0 ≤ marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S) ∧
            ‖marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S)‖ ≤ ε n) ∧
          (∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
            Summable (fun τ : CriticalZeros => ‖if τ ∈ (F n) then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
            (∑' τ : CriticalZeros, ‖if τ ∈ (F n) then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < ε n)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
          ‖canonicalTailCovariance t ht (F n)‖ < δ ∧
          (∀ ν : ℝ, μ n ≤ ν → ‖marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S)‖ < δ) ∧
          (∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
            (∑' τ : CriticalZeros, ‖if τ ∈ F n then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < δ)) ∧
      (∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        Tendsto (fun n => marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
              (canonicalSelectedSynthesis t ht S))
          atTop (nhds (canonicalPicardMarker t ht S))) ∧
      (∀ c : ℝ, ∀ hc : 0 ≤ c, c < T → ∀ δ : ℝ, 0 < δ →
        ∃ d : ℝ, 0 < d ∧ c + d ≤ T ∧
          ∀ t : ℝ, ∀ ht : 0 < t, c < t → t < c + d →
            ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
              ‖marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
              (canonicalSelectedSynthesis t ht S) - canonicalSupportRightMarker c hc S‖ < δ) ∧
      (∀ c : ℝ, ∀ hc : 0 ≤ c, c < T →
        ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc S ↔
          ∀ η : ℝ, 0 < η → η < 1 / 2 →
      ∃ d : ℝ, 0 < d ∧ c + d ≤ T ∧
        ∀ t : ℝ, ∀ ht : 0 < t, c < t → t < c + d →
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            ∀ g : ℝ → ℂ, SupportedTest t g →
              ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 ≤
                ((1 / 2 - η)⁻¹ - 1) * (((weilDistribution (conv g (starInv g))).re) +
                  ‖(canonicalSelectedSynthesis t ht (F n)).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 +
                  μ n * ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) +
                    (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2))))) ∧
      (∀ c : ℝ, ∀ hc : 0 ≤ c, c < T →
        ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc S ↔
          ∀ η : ℝ, 0 < η → η < 1 / 2 →
      ∃ d : ℝ, 0 < d ∧ c + d ≤ T ∧
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ∀ t : ℝ, ∀ ht : 0 < t, c < t → t < c + d →
            ∀ g : ℝ → ℂ, SupportedTest t g →
              ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 ≤
                ((1 / 2 - η)⁻¹ - 1) * (((weilDistribution (conv g (starInv g))).re) +
                  ‖(canonicalSelectedSynthesis t ht (F n)).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 +
                  μ n * ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) +
                    (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2))))) := by sorry
