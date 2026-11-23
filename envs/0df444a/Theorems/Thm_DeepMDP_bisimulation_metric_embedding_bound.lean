-- Prove2me | Theorems.Thm_DeepMDP_bisimulation_metric_embedding_bound
-- name    : DeepMDP.bisimulation_metric_embedding_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:32:14.563803+00:00
-- url     : https://prove2.me/theorems/bdf838d6-00b8-4e60-98e0-01bebba1c615
-- title:
--   Lemma 5: bisimulation distance between a state and its embedding
-- statement:
--   Let $M$, $\bar M$ and $\phi$ be as in Theorem 3. Consider the MDP on $S\sqcup\bar S$ obtained by joining $M$ and $\bar M$: when an action is taken, each state is rewarded and transitions according to its own MDP. Let $\tilde d$ be its bisimulation metric. Then for every $s\in S$,
--
--   $$\tilde d(s,\phi(s))\le L^\infty_{\bar R}+\gamma L^\infty_{\bar P}\,\frac{K_{\bar R}}{1-\gamma K_{\bar P}}.$$
--
--   **Formalization Note** The joined MDP is built explicitly on the disjoint union $S\oplus\bar S$, with the transitions of $M$ and $\bar M$ pushed forward by the two inclusions. Its bisimulation metric is the limit of the iterates of Definition 5. The comparison is made in $[0,\infty]$, with $0\cdot\infty=0$. This is harmless: if $K_{\bar R}=0$, all latent states are bisimilar and the bound reduces to $L^\infty_{\bar R}$, which still holds.
-- source:
--   Gelada, Kumar, Buckman, Nachum and Bellemare, DeepMDP: Learning Continuous Latent Space Models for Representation Learning, arXiv:1906.02736v1 (ICML 2019), Appendix A.4, Lemma 5, p. 19; Definition 5, Section 5.2, p. 6

import Mathlib
import Definitions.Def_DeepMDP_Basic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace DeepMDP

theorem bisimulation_metric_embedding_bound {S Sb A : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    [MetricSpace Sb] [MeasurableSpace Sb] [BorelSpace Sb] [SecondCountableTopology Sb]
    [CompleteSpace Sb]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (R : S → A → ℝ) (P : A → Kernel S S) (Rb : Sb → A → ℝ) (Pb : A → Kernel Sb Sb) (γ : ℝ)
    (φ : S → Sb) (hM : IsMDP R P γ) (hMb : IsMDP Rb Pb γ)
    (KRb KPb : ℝ≥0) (hLip : IsLipschitzMDP Rb Pb KRb KPb) (hA1 : γ * (KPb : ℝ) < 1) (s : S) :
    bisimMetric (joinReward R Rb) (joinTrans P Pb) γ (.inl s) (.inr (φ s)) ≤
      rewardLossGlobal R Rb φ +
        ENNReal.ofReal γ * transLossGlobal P Pb φ * ENNReal.ofReal (KRb / (1 - γ * KPb)) := by sorry

end DeepMDP
