-- Prove2me | Theorems.Thm_DeepMDP_local_value_difference_bound
-- name    : DeepMDP.local_value_difference_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:29:17.872923+00:00
-- url     : https://prove2.me/theorems/3ab3d93a-ba25-4ed3-ba7e-bcb22e7d94c5
-- title:
--   Lemma 3: local value difference bound
-- statement:
--   Let $M$, $\bar M$ and $\phi$ be as in Lemma 2 (countable discrete $S$, metric $\bar S$, finite $A$, $0\le\gamma<1$, bounded measurable rewards), with $\bar M$ $(K_{\bar R},K_{\bar P})$-Lipschitz and $\gamma K_{\bar P}<1$ (Assumption 1). Let $\bar\pi$ be a $K_{\bar V}$-Lipschitz-valued policy, let $\xi$ be a stationary distribution of $\bar\pi$ in $M$, and let $\xi_{\bar\pi}(s,a)=\xi(s)\bar\pi(a|\phi(s))$. With the local losses $L^{\xi_{\bar\pi}}_{\bar R}$ and $L^{\xi_{\bar\pi}}_{\bar P}$ measured under $\xi_{\bar\pi}$,
--
--   $$\mathbb E_{(s,a)\sim\xi_{\bar\pi}}\big|Q^{\bar\pi}(s,a)-\bar Q^{\bar\pi}(\phi(s),a)\big|\le\frac{L^{\xi_{\bar\pi}}_{\bar R}+\gamma K_{\bar V}L^{\xi_{\bar\pi}}_{\bar P}}{1-\gamma}.$$
--
--   This is the form of the guarantee that can be optimised by stochastic gradient methods, since the losses are expectations.
--
--   **Formalization Note** The expectations are integrals of nonnegative functions with values in $[0,\infty]$. The statement holds for every stationary distribution of the policy, which is what the proof uses.
-- source:
--   Gelada, Kumar, Buckman, Nachum and Bellemare, DeepMDP: Learning Continuous Latent Space Models for Representation Learning, arXiv:1906.02736v1 (ICML 2019), Section 4.1, Lemma 3, p. 5; proof via Lemma 8, Appendix A.6, pp. 21-22

import Mathlib
import Definitions.Def_DeepMDP_Basic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace DeepMDP

theorem local_value_difference_bound {S Sb A : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    [MetricSpace Sb] [MeasurableSpace Sb] [BorelSpace Sb]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (R : S → A → ℝ) (P : A → Kernel S S) (Rb : Sb → A → ℝ) (Pb : A → Kernel Sb Sb) (γ : ℝ)
    (φ : S → Sb) (hM : IsMDP R P γ) (hMb : IsMDP Rb Pb γ)
    (KRb KPb : ℝ≥0) (hLip : IsLipschitzMDP Rb Pb KRb KPb) (hA1 : γ * (KPb : ℝ) < 1)
    (πb : Kernel Sb A) [IsMarkovKernel πb] (KV : ℝ≥0) (hπ : IsLipschitzValued Rb Pb γ πb KV)
    (ξ : Measure S) (hξ : IsStationary P (liftPolicy πb φ) ξ) :
    ∫⁻ z, ENNReal.ofReal |qValue R P γ (liftPolicy πb φ) z.1 z.2 - qValue Rb Pb γ πb (φ z.1) z.2|
        ∂(stateActionDist ξ (liftPolicy πb φ)) ≤
      (rewardLossLocal (stateActionDist ξ (liftPolicy πb φ)) R Rb φ +
        ENNReal.ofReal γ * (KV : ℝ≥0∞) * transLossLocal (stateActionDist ξ (liftPolicy πb φ)) P Pb φ) /
        ENNReal.ofReal (1 - γ) := by sorry

end DeepMDP
