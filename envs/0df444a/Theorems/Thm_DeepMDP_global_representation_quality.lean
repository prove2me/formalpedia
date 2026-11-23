-- Prove2me | Theorems.Thm_DeepMDP_global_representation_quality
-- name    : DeepMDP.global_representation_quality
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:28:37.225778+00:00
-- url     : https://prove2.me/theorems/f25ba4b4-0b11-4720-8888-be71fb947d2a
-- title:
--   Theorem 1: global representation quality bound
-- statement:
--   Let $M=\langle S,A,R,P,\gamma\rangle$ be an MDP with countable discrete state space, and let $\bar M=\langle\bar S,A,\bar R,\bar P,\gamma\rangle$ be a DeepMDP on a metric space $(\bar S,d_{\bar S})$, both with finite action set $A$, discount $0\le\gamma<1$ and bounded measurable rewards, with an embedding $\phi:S\to\bar S$ and global losses $L^\infty_{\bar R},L^\infty_{\bar P}$. Assume $\bar M$ is $(K_{\bar R},K_{\bar P})$-Lipschitz with $\gamma K_{\bar P}<1$ (Assumption 1). For every $K_{\bar V}$-Lipschitz-valued policy $\bar\pi$, all $s_1,s_2\in S$ and all $a\in A$,
--
--   $$\big|Q^{\bar\pi}(s_1,a)-Q^{\bar\pi}(s_2,a)\big|\le K_{\bar V}\,d_{\bar S}(\phi(s_1),\phi(s_2))+2\,\frac{L^\infty_{\bar R}+\gamma K_{\bar V}L^\infty_{\bar P}}{1-\gamma},$$
--
--   where $Q^{\bar\pi}$ is the action value in $M$ of the policy $s\mapsto\bar\pi(\cdot|\phi(s))$.
--
--   When both global losses vanish, states with different values for such a policy are never mapped to the same latent point, which justifies using $\phi$ as a representation for value prediction.
--
--   **Formalization Note** Both sides are compared in $[0,\infty]$, with $0\cdot\infty=0$. This is harmless, as in Lemma 2: $K_{\bar V}=0$ makes $\bar V^{\bar\pi}$ constant. Assumption 1 is a standing assumption of the paper from Section 2.4 onwards and is included though the proof does not use it.
-- source:
--   Gelada, Kumar, Buckman, Nachum and Bellemare, DeepMDP: Learning Continuous Latent Space Models for Representation Learning, arXiv:1906.02736v1 (ICML 2019), Section 3.2, Theorem 1, p. 4; proof in Appendix A.2, p. 17

import Mathlib
import Definitions.Def_DeepMDP_Basic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace DeepMDP

theorem global_representation_quality {S Sb A : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    [MetricSpace Sb] [MeasurableSpace Sb] [BorelSpace Sb]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (R : S → A → ℝ) (P : A → Kernel S S) (Rb : Sb → A → ℝ) (Pb : A → Kernel Sb Sb) (γ : ℝ)
    (φ : S → Sb) (hM : IsMDP R P γ) (hMb : IsMDP Rb Pb γ)
    (KRb KPb : ℝ≥0) (hLip : IsLipschitzMDP Rb Pb KRb KPb) (hA1 : γ * (KPb : ℝ) < 1)
    (πb : Kernel Sb A) [IsMarkovKernel πb] (KV : ℝ≥0) (hπ : IsLipschitzValued Rb Pb γ πb KV)
    (s₁ s₂ : S) (a : A) :
    ENNReal.ofReal |qValue R P γ (liftPolicy πb φ) s₁ a - qValue R P γ (liftPolicy πb φ) s₂ a| ≤
      (KV : ℝ≥0∞) * edist (φ s₁) (φ s₂) +
        2 * ((rewardLossGlobal R Rb φ + ENNReal.ofReal γ * (KV : ℝ≥0∞) * transLossGlobal P Pb φ) /
          ENNReal.ofReal (1 - γ)) := by sorry

end DeepMDP
