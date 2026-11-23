-- Prove2me | Theorems.Thm_DeepMDP_local_representation_quality
-- name    : DeepMDP.local_representation_quality
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:29:53.760683+00:00
-- url     : https://prove2.me/theorems/ef1d92c1-fbca-4e85-bada-23efaab37abb
-- title:
--   Theorem 2: local representation quality bound
-- statement:
--   Let $M$, $\bar M$, $\phi$, $\bar\pi$, $K_{\bar V}$ and the stationary distribution $\xi$ of $\bar\pi$ in $M$ be as in Lemma 3, with local losses measured under $\xi_{\bar\pi}(s,a)=\xi(s)\bar\pi(a|\phi(s))$. For any two states $s_1,s_2\in S$ with $\xi(s_1)>0$ and $\xi(s_2)>0$,
--
--   $$\big|V^{\bar\pi}(s_1)-V^{\bar\pi}(s_2)\big|\le K_{\bar V}\,d_{\bar S}(\phi(s_1),\phi(s_2))+\frac{L^{\xi_{\bar\pi}}_{\bar R}+\gamma K_{\bar V}L^{\xi_{\bar\pi}}_{\bar P}}{1-\gamma}\left(\frac1{\xi(s_1)}+\frac1{\xi(s_2)}\right).$$
--
--   The representation guarantee of Theorem 1 thus holds for states that the policy visits often.
--
--   **Formalization Note** The paper writes $d_{\bar\pi}(s)$, which it does not define. The proof uses $d_{\bar\pi}(s)=\xi_{\bar\pi}(s)$, the stationary probability of $s$, and that is what is formalized. The paper's expression $1/d_{\bar\pi}(s)$ requires $\xi(s)>0$, which is a hypothesis here. Both sides are compared in $[0,\infty]$.
-- source:
--   Gelada, Kumar, Buckman, Nachum and Bellemare, DeepMDP: Learning Continuous Latent Space Models for Representation Learning, arXiv:1906.02736v1 (ICML 2019), Section 4.2, Theorem 2, p. 5; proof in Appendix A.3, pp. 17-18

import Mathlib
import Definitions.Def_DeepMDP_Basic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace DeepMDP

theorem local_representation_quality {S Sb A : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    [MetricSpace Sb] [MeasurableSpace Sb] [BorelSpace Sb]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (R : S → A → ℝ) (P : A → Kernel S S) (Rb : Sb → A → ℝ) (Pb : A → Kernel Sb Sb) (γ : ℝ)
    (φ : S → Sb) (hM : IsMDP R P γ) (hMb : IsMDP Rb Pb γ)
    (KRb KPb : ℝ≥0) (hLip : IsLipschitzMDP Rb Pb KRb KPb) (hA1 : γ * (KPb : ℝ) < 1)
    (πb : Kernel Sb A) [IsMarkovKernel πb] (KV : ℝ≥0) (hπ : IsLipschitzValued Rb Pb γ πb KV)
    (ξ : Measure S) (hξ : IsStationary P (liftPolicy πb φ) ξ)
    (s₁ s₂ : S) (h₁ : 0 < ξ {s₁}) (h₂ : 0 < ξ {s₂}) :
    ENNReal.ofReal |vValue R P γ (liftPolicy πb φ) s₁ - vValue R P γ (liftPolicy πb φ) s₂| ≤
      (KV : ℝ≥0∞) * edist (φ s₁) (φ s₂) +
        (rewardLossLocal (stateActionDist ξ (liftPolicy πb φ)) R Rb φ +
          ENNReal.ofReal γ * (KV : ℝ≥0∞) * transLossLocal (stateActionDist ξ (liftPolicy πb φ)) P Pb φ) /
          ENNReal.ofReal (1 - γ) * ((ξ {s₁})⁻¹ + (ξ {s₂})⁻¹) := by sorry

end DeepMDP
