-- Prove2me | Theorems.Thm_DeepMDP_bisimulation_metric_upper_bound
-- name    : DeepMDP.bisimulation_metric_upper_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:32:48.858408+00:00
-- url     : https://prove2.me/theorems/e9bb55a3-3914-4980-982f-c0d492f22591
-- title:
--   Theorem 3: the embedding and the losses bound the bisimulation metric
-- statement:
--   Let $M=\langle S,A,R,P,\gamma\rangle$ be an MDP with countable discrete state space and $\bar M=\langle\bar S,A,\bar R,\bar P,\gamma\rangle$ a DeepMDP on a complete separable metric space $(\bar S,d_{\bar S})$, both with finite action set, discount $0\le\gamma<1$ and bounded measurable rewards. Let $\phi:S\to\bar S$ be an embedding with global losses $L^\infty_{\bar R}$ and $L^\infty_{\bar P}$. Assume $\bar M$ is $(K_{\bar R},K_{\bar P})$-Lipschitz with $\gamma K_{\bar P}<1$ (Assumption 1). Then the bisimulation metric $\tilde d$ of $M$ satisfies, for all $s_1,s_2\in S$,
--
--   $$\tilde d(s_1,s_2)\le\frac{(1-\gamma)K_{\bar R}}{1-\gamma K_{\bar P}}\,d_{\bar S}(\phi(s_1),\phi(s_2))+2\left(L^\infty_{\bar R}+\gamma L^\infty_{\bar P}\,\frac{K_{\bar R}}{1-\gamma K_{\bar P}}\right).$$
--
--   In particular, when both global losses vanish, the embedding never maps two states at positive bisimulation distance to the same point.
--
--   **Formalization Note** The printed constant is $(1-\gamma)K_R/(1-\gamma K_{\bar P})$, where $K_R$ is not defined for $M$; the proof (Lemma 4) gives $K_{\bar R}$, which is used here. The bisimulation metric is the limit of the iterates of Definition 5. The latent space is taken Polish, the setting of Ferns et al. (2011). The comparison is made in $[0,\infty]$, with $0\cdot\infty=0$. This is harmless: if $K_{\bar R}=0$, every latent state is bisimilar to every other, so an infinite transition loss contributes nothing; if $\gamma=0$, transitions play no role.
-- source:
--   Gelada, Kumar, Buckman, Nachum and Bellemare, DeepMDP: Learning Continuous Latent Space Models for Representation Learning, arXiv:1906.02736v1 (ICML 2019), Section 5.3, Theorem 3, p. 6; proof in Appendix A.4, p. 20

import Mathlib
import Definitions.Def_DeepMDP_Basic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace DeepMDP

theorem bisimulation_metric_upper_bound {S Sb A : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    [MetricSpace Sb] [MeasurableSpace Sb] [BorelSpace Sb] [SecondCountableTopology Sb]
    [CompleteSpace Sb]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (R : S → A → ℝ) (P : A → Kernel S S) (Rb : Sb → A → ℝ) (Pb : A → Kernel Sb Sb) (γ : ℝ)
    (φ : S → Sb) (hM : IsMDP R P γ) (hMb : IsMDP Rb Pb γ)
    (KRb KPb : ℝ≥0) (hLip : IsLipschitzMDP Rb Pb KRb KPb) (hA1 : γ * (KPb : ℝ) < 1) (s₁ s₂ : S) :
    bisimMetric R (fun s a => P a s) γ s₁ s₂ ≤
      ENNReal.ofReal ((1 - γ) * KRb / (1 - γ * KPb)) * edist (φ s₁) (φ s₂) +
        2 * (rewardLossGlobal R Rb φ +
          ENNReal.ofReal γ * transLossGlobal P Pb φ * ENNReal.ofReal (KRb / (1 - γ * KPb))) := by sorry

end DeepMDP
