-- Prove2me | Theorems.Thm_ConnesGreen_canonical_uniform_finite_negative_weil_certificates
-- name    : ConnesGreen.canonical_uniform_finite_negative_weil_certificates
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T19:24:27.860559+00:00
-- url     : https://prove2.me/theorems/3041635c-300d-4669-b7e6-890c06962d34
-- title:
--   Uniform actual-zero truncation and robust finite certificates for negative Weil values
-- statement:
--   # Robust finite actual-zero certificates for a negative Weil value
--
--   For every bounded positive support range T, fixed original finite actual-zero packet S, finite requests K_n and explicit positive vanishing schedules μ_n, ε_n with ε_n<1, there is one nested reflection-closed restoration sequence F_n containing S and K_n. All preceding tail estimates, ordered endpoint limits and arithmetic equivalences remain valid for that same sequence.
--
--   Write
--   $$
--   P_n(g)=\sum_{\rho\in F_n} m_\rho\widehat{g*g^*}(\rho),\qquad Q(g)=\operatorname{Re}W(g*g^*).
--   $$
--   For every n, every 0<t≤T and every original SupportedTest t g with ‖sourceEmbed(t,problemOneL(g))‖²≤1,
--   $$|Q(g)-\operatorname{Re}P_n(g)|<\varepsilon_n.$$
--   This error bound holds simultaneously over the full bounded support range and all normalized original tests, with F_n chosen first.
--
--   For every such t and g, the following three conditions are equivalent:
--
--   - Q(g)<0;
--   - there exists n with Re P_n(g)<−ε_n;
--   - there exists N such that every n≥N has Re P_n(g)<−ε_n.
--
--   The finite sum uses actual critical-strip zeta zeros, their actual multiplicities and the original Mellin transform. It is not a surrogate quadratic form. A finite negative sum without a margin exceeding ε_n is not a certificate here. The selected actor S is preserved in all inherited marker statements; F_n is a restoration packet, not a replacement selected actor.
--
--   The theorem does not construct a negative test, prove an off-critical-line separating test, establish the arithmetic endpoint lower bound, give an effective zero-height cutoff or prove RH. The stage witnessing negativity may depend on the test and its strict margin. The normalized test hypothesis is explicit; no claim for unnormalized tests is added.
-- source:
--   # Finite-to-full tail verification closed
--
--   For every bounded positive support range T, fixed original finite actual-zero packet S, finite requests K_n and explicit positive vanishing schedules μ_n, ε_n with ε_n<1, there is one nested reflection-closed restoration sequence F_n containing S and K_n. All preceding tail estimates, ordered endpoint limits and arithmetic equivalences remain valid for that same sequence.
--
--   Write
--   $$
--   P_n(g)=\sum_{\rho\in F_n} m_\rho\widehat{g*g^*}(\rho),\qquad Q(g)=\operatorname{Re}W(g*g^*).
--   $$
--   For every n, every 0<t≤T and every original SupportedTest t g with ‖sourceEmbed(t,problemOneL(g))‖²≤1,
--   $$|Q(g)-\operatorname{Re}P_n(g)|<\varepsilon_n.$$
--   This error bound holds simultaneously over the full bounded support range and all normalized original tests, with F_n chosen first.
--
--   For every such t and g, the following three conditions are equivalent:
--
--   - Q(g)<0;
--   - there exists n with Re P_n(g)<−ε_n;
--   - there exists N such that every n≥N has Re P_n(g)<−ε_n.
--
--   The finite sum uses actual critical-strip zeta zeros, their actual multiplicities and the original Mellin transform. It is not a surrogate quadratic form. A finite negative sum without a margin exceeding ε_n is not a certificate here. The selected actor S is preserved in all inherited marker statements; F_n is a restoration packet, not a replacement selected actor.
--
--   The theorem does not construct a negative test, prove an off-critical-line separating test, establish the arithmetic endpoint lower bound, give an effective zero-height cutoff or prove RH. The stage witnessing negativity may depend on the test and its strict margin. The normalized test hypothesis is explicit; no claim for unnormalized tests is added.
--
--   The accepted predecessor supplies the nested sequence and its uniformly bounded absolute actual-zero tails. Applying the certified original explicit formula to g*g* gives the complete HasSum with value W(g*g*). Smoothness and compact support of this convolution are proved directly from the original test predicate.
--
--   Split that HasSum into its finite head on F_n and its zero-masked complement. Thus the complement has sum W(g*g*)−P_n(g). The norm of this complement sum is at most the sum of the norms of its terms; the absolute real part is at most the complex norm. The inherited normalized actual-zero tail bound is strictly less than ε_n. This proves the uniform real-error inequality.
--
--   For the numeric certificate equivalence, write q=Q(g) and a_n=Re P_n(g). If q<0, choose N so that ε_n<−q/2 for every n≥N. The error inequality gives a_n<q+ε_n<−ε_n. Conversely, if a_n<−ε_n at any stage, q<a_n+ε_n<0. An eventual certificate supplies a certificate at n=N. No negative test or desired separation assertion is assumed by the primary theorem: each negative statement is an equivalent condition, proved in both directions.
--
--   Native certification expands the complete preceding assembly plus the new reduction over the pinned certified repository module closure. Platform imports exactly the two accepted dependencies. No source theorem, actual-zero definition, actor or theorem cursor is modified. The finite packets are existential rather than claimed effective or numerically computable cutoffs.

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

theorem ConnesGreen.canonical_uniform_finite_negative_weil_certificates
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
                    (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2))))) ∧
      (∀ n : ℕ, ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
          |(weilDistribution (conv g (starInv g))).re - (∑ τ ∈ F n, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re| < ε n) ∧
      (∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
          (((weilDistribution (conv g (starInv g))).re < 0 ↔ ∃ n : ℕ, (∑ τ ∈ F n, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re < -ε n) ∧
           ((weilDistribution (conv g (starInv g))).re < 0 ↔ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (∑ τ ∈ F n, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re < -ε n))) := by sorry
