-- Prove2me | Theorems.Thm_ConnesGreen_canonical_energy_scaled_finite_negative_weil_certificates
-- name    : ConnesGreen.canonical_energy_scaled_finite_negative_weil_certificates
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T19:40:34.279388+00:00
-- url     : https://prove2.me/theorems/0eec276e-f8c5-4401-bdf6-4d93d4727ca6
-- title:
--   Energy-scaled full actual-zero tails and finite negative Weil certificates for every original test
-- statement:
--   # Energy-scaled actual-zero tails and finite Weil certificates
--
--   For every positive bounded support range T, original finite actual-zero selected packet S, finite requests K_n and explicit positive vanishing schedules μ_n and ε_n with ε_n<1, there exists one nested reflection-closed restoration sequence F_n containing S and K_n. Every preceding marker, tail, ordered-endpoint and normalized-certificate clause is retained unchanged for this same F.
--
--   For every original SupportedTest t g with 0<t≤T, define
--   $$E_t(g)=\|\operatorname{sourceEmbed}(t,Lg)\|^2,\qquad P_n(g)=\sum_{\rho\in F_n}m_\rho\widehat{g*g^*}(\rho).$$
--   There is no norm restriction on g in the new clauses. For every n, the norm family of the actual-zero complement is summable and
--   $$
--   \sum_{\rho\notin F_n}\left|m_\rho\widehat{g*g^*}(\rho)\right|\le\varepsilon_n E_t(g),\qquad
--   \|W(g*g^*)-P_n(g)\|\le\varepsilon_n E_t(g).
--   $$
--   The cutoff sequence is chosen before the support windows and tests. The energy is the original physical source norm squared; it is not a new test norm or an assumed external seminorm. The non-strict bound includes E_t(g)=0.
--
--   For every such original test, all three conditions are equivalent:
--
--   - Re W(g*g*)<0;
--   - some n has Re P_n(g)<−ε_n E_t(g);
--   - some N has Re P_n(g)<−ε_n E_t(g) for every n≥N.
--
--   Moreover, P_n(g) converges in ℂ to W(g*g*) for every such fixed test and support. No enumeration or exhaustion of the complete zero set is assumed. No common convergence stage over tests of unbounded energy is claimed: the uniform quantitative inequality carries its explicit energy factor.
--
--   The original selected actor remains S. F_n remains a restoration packet. All sums use actual critical-strip zeta zeros, actual multiplicities and the original Mellin transform. No negative test, quartet-separating margin, unconditional arithmetic half-bound, effective height cutoff or RH theorem is supplied.
-- source:
--   # Full-tail verification for arbitrary original test size
--
--   For every positive bounded support range T, original finite actual-zero selected packet S, finite requests K_n and explicit positive vanishing schedules μ_n and ε_n with ε_n<1, there exists one nested reflection-closed restoration sequence F_n containing S and K_n. Every preceding marker, tail, ordered-endpoint and normalized-certificate clause is retained unchanged for this same F.
--
--   For every original SupportedTest t g with 0<t≤T, define
--   $$E_t(g)=\|\operatorname{sourceEmbed}(t,Lg)\|^2,\qquad P_n(g)=\sum_{\rho\in F_n}m_\rho\widehat{g*g^*}(\rho).$$
--   There is no norm restriction on g in the new clauses. For every n, the norm family of the actual-zero complement is summable and
--   $$
--   \sum_{\rho\notin F_n}\left|m_\rho\widehat{g*g^*}(\rho)\right|\le\varepsilon_n E_t(g),\qquad
--   \|W(g*g^*)-P_n(g)\|\le\varepsilon_n E_t(g).
--   $$
--   The cutoff sequence is chosen before the support windows and tests. The energy is the original physical source norm squared; it is not a new test norm or an assumed external seminorm. The non-strict bound includes E_t(g)=0.
--
--   For every such original test, all three conditions are equivalent:
--
--   - Re W(g*g*)<0;
--   - some n has Re P_n(g)<−ε_n E_t(g);
--   - some N has Re P_n(g)<−ε_n E_t(g) for every n≥N.
--
--   Moreover, P_n(g) converges in ℂ to W(g*g*) for every such fixed test and support. No enumeration or exhaustion of the complete zero set is assumed. No common convergence stage over tests of unbounded energy is claimed: the uniform quantitative inequality carries its explicit energy factor.
--
--   The original selected actor remains S. F_n remains a restoration packet. All sums use actual critical-strip zeta zeros, actual multiplicities and the original Mellin transform. No negative test, quartet-separating margin, unconditional arithmetic half-bound, effective height cutoff or RH theorem is supplied.
--
--   For each original test vector x, Cauchy–Schwarz gives |⟨u,x⟩|²≤‖u‖²‖x‖². Applying this to the square-norm-summable original positive and negative columns proves summability of their pairing energies for arbitrary x. The existing exact actual-zero term estimate bounds each convolved spectral norm by its positive plus negative pairing energy.
--
--   On the complement of F_n, adjoint Parseval identities identify those two energy sums with ‖P_tail* x‖² and ‖B_F_n* x‖². Each is at most its covariance operator norm times ‖x‖². Therefore the full actual-zero absolute tail is at most (‖P_tail P_tail*‖+‖B_F_n B_F_n*‖)‖x‖², and the inherited uniform covariance estimate bounds this by ε_n‖x‖². No division by ‖x‖ and no nonzero-vector assumption is used.
--
--   The original explicit formula and exact finite/complement HasSum decomposition then bound the complex finite-sum error by that same absolute tail. For fixed x, ε_n‖x‖² tends to zero. This proves convergence of the complex finite sums even though no full-zero exhaustion is asserted.
--
--   For the sign criterion let q=Re W(g*g*) and a_n=Re P_n(g). If q<0, choose N so that ε_n E_t(g)<−q/2 for every n≥N. From |q−a_n|≤ε_n E_t(g) obtain a_n≤q+ε_n E_t(g)<−ε_n E_t(g). Conversely a_n<−ε_n E_t(g) implies q≤a_n+ε_n E_t(g)<0. An eventual certificate supplies a certificate at n=N. The main theorem does not assume any of these negative conditions; it proves their equivalence.
--
--   The previous normalized-test theorem is preserved in full. The new bounds and certificate equivalences apply to every original supported test. The fixed energy factor records the actual dependence instead of hiding it in a normalization premise. All helpers are ordinary proved Lean declarations, and all convergence and actor hypotheses in them are discharged in the main theorem. No new definition, source-theorem change or project axiom is introduced.

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

theorem ConnesGreen.canonical_energy_scaled_finite_negative_weil_certificates
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
           ((weilDistribution (conv g (starInv g))).re < 0 ↔ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (∑ τ ∈ F n, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re < -ε n))) ∧
      (∀ n : ℕ, ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∀ g : ℝ → ℂ, SupportedTest t g →
          Summable (fun τ : CriticalZeros => ‖if τ ∈ F n then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
          (∑' τ : CriticalZeros, ‖if τ ∈ F n then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ≤ ε n * ‖sourceEmbed t (problemOneL g)‖ ^ 2 ∧
          ‖(weilDistribution (conv g (starInv g))) - (∑ τ ∈ F n, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1)‖ ≤ ε n * ‖sourceEmbed t (problemOneL g)‖ ^ 2) ∧
      (∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∀ g : ℝ → ℂ, SupportedTest t g →
          (((weilDistribution (conv g (starInv g))).re < 0 ↔ ∃ n : ℕ, (∑ τ ∈ F n, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re < -(ε n * ‖sourceEmbed t (problemOneL g)‖ ^ 2)) ∧
           ((weilDistribution (conv g (starInv g))).re < 0 ↔ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (∑ τ ∈ F n, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re < -(ε n * ‖sourceEmbed t (problemOneL g)‖ ^ 2)) ∧
           Tendsto (fun n => (∑ τ ∈ F n, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1)) atTop (nhds ((weilDistribution (conv g (starInv g))))))) := by sorry
