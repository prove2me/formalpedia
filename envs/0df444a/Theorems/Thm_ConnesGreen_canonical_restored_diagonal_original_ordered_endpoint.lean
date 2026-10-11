-- Prove2me | Theorems.Thm_ConnesGreen_canonical_restored_diagonal_original_ordered_endpoint
-- name    : ConnesGreen.canonical_restored_diagonal_original_ordered_endpoint
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T18:20:15.01537+00:00
-- url     : https://prove2.me/theorems/12ae3865-2cba-4e37-84dd-bcfc45c8df31
-- title:
--   Finite-restored actual-zero markers recover the original ordered support endpoint
-- statement:
--   Fix $T>0$, a finite selected packet $S$ of actual critical-strip zeta zeros, arbitrary finite requested packets $K_n$, and prescribed positive numerical schedules $\mu_n\to0$ and $0<\varepsilon_n<1$ with $\varepsilon_n\to0$. There exist nested reflection-closed finite actual-zero cutoffs $F_n\supseteq S\cup K_n$ retaining all conclusions of the preceding diagonal theorem: exact original positive-tail columns, covariance norm sum $<\varepsilon_n$, complete actual spectral norm tail summability and sum $<\varepsilon_n$ for every original normalized supported test, and nonnegative original selected-marker error of norm at most $\varepsilon_n$ for every regularization above $\mu_n$, uniformly on $0<t\le T$.
--
--   Write $L_t$ for the original full-positive covariance, $R_{F_n,t}$ for the original negative covariance outside $F_n$, $N_{S,t}$ for the unchanged original selected synthesis, and
--   $$
--   A_n(t)=\operatorname{marker}(L_t+\mu_n I-R_{F_n,t},N_{S,t}).
--   $$
--   For every fixed $0<t\le T$, these restored markers converge in operator norm to the original Picard marker:
--   $$
--   A_n(t)\longrightarrow\operatorname{canonicalPicardMarker}(t,S).
--   $$
--   For every $0\le c<T$, let $G_c$ be the original support-right marker, defined by first taking the positive-regularization Picard limit and then taking the support radius to $c$ from the right. The restored markers recover that same ordered endpoint with the following exact quantifiers:
--   $$
--   \forall\delta>0\;\exists d>0,\ c+d\le T:\quad
--   \forall t\in(c,c+d)\;\exists N\;\forall n\ge N,\quad
--   \|A_n(t)-G_c\|<\delta.
--   $$
--   The inner index may depend on the window. This identifies the finite-restored inner limit and its ordered outer endpoint without exchanging limits. It does not assert a uniform inner index over the outer windows, a prescribed joint diagonal limit, an arithmetic half-bound, critical-window location, quartet domination, or RH. All carriers, multiplicities, transforms and selected actors are the original ones.
-- source:
--   Fix $T>0$, a finite selected packet $S$ of actual critical-strip zeta zeros, arbitrary finite requested packets $K_n$, and prescribed positive numerical schedules $\mu_n\to0$ and $0<\varepsilon_n<1$ with $\varepsilon_n\to0$. There exist nested reflection-closed finite actual-zero cutoffs $F_n\supseteq S\cup K_n$ retaining all conclusions of the preceding diagonal theorem: exact original positive-tail columns, covariance norm sum $<\varepsilon_n$, complete actual spectral norm tail summability and sum $<\varepsilon_n$ for every original normalized supported test, and nonnegative original selected-marker error of norm at most $\varepsilon_n$ for every regularization above $\mu_n$, uniformly on $0<t\le T$.
--
--   Write $L_t$ for the original full-positive covariance, $R_{F_n,t}$ for the original negative covariance outside $F_n$, $N_{S,t}$ for the unchanged original selected synthesis, and
--   $$
--   A_n(t)=\operatorname{marker}(L_t+\mu_n I-R_{F_n,t},N_{S,t}).
--   $$
--   For every fixed $0<t\le T$, these restored markers converge in operator norm to the original Picard marker:
--   $$
--   A_n(t)\longrightarrow\operatorname{canonicalPicardMarker}(t,S).
--   $$
--   For every $0\le c<T$, let $G_c$ be the original support-right marker, defined by first taking the positive-regularization Picard limit and then taking the support radius to $c$ from the right. The restored markers recover that same ordered endpoint with the following exact quantifiers:
--   $$
--   \forall\delta>0\;\exists d>0,\ c+d\le T:\quad
--   \forall t\in(c,c+d)\;\exists N\;\forall n\ge N,\quad
--   \|A_n(t)-G_c\|<\delta.
--   $$
--   The inner index may depend on the window. This identifies the finite-restored inner limit and its ordered outer endpoint without exchanging limits. It does not assert a uniform inner index over the outer windows, a prescribed joint diagonal limit, an arithmetic half-bound, critical-window location, quartet domination, or RH. All carriers, multiplicities, transforms and selected actors are the original ones.
--
--   The preceding nested actual-zero theorem supplies all cutoff, spectral and relative covariance estimates. The original finite-selected marker norm-limit theorem supplies the inner Picard limit, and the original actual-zero support-right-limit theorem supplies the outer limit. New named lemmas transport a vanishing norm error to the original inner limit and then prove the explicit ordered approximation. No limit-existence premise, assumed endpoint equality, arithmetic premise, new project axiom or admission is introduced. The numerical schedule hypotheses are explicit. Standalone proof at clean unchanged native head ada7948cb459fd21d400cd8f2a92e87672e31f2d; no new repository commit or CI head. Original RPB108 original-form attachments remain future formalization work.

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

theorem ConnesGreen.canonical_restored_diagonal_original_ordered_endpoint
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
              (canonicalSelectedSynthesis t ht S) - canonicalSupportRightMarker c hc S‖ < δ) := by sorry
