-- Prove2me | Theorems.Thm_DeepMDP_global_value_difference_bound
-- name    : DeepMDP.global_value_difference_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:27:47.678651+00:00
-- url     : https://prove2.me/theorems/7011c3ca-59b8-4b27-b0e2-75d638812094
-- title:
--   Lemma 2: global value difference bound
-- statement:
--   Let $M=\langle S,A,R,P,\gamma\rangle$ be an MDP with countable discrete state space, and let $\bar M=\langle\bar S,A,\bar R,\bar P,\gamma\rangle$ be a DeepMDP on a metric space $(\bar S,d_{\bar S})$, both with finite action set $A$, discount $0\le\gamma<1$ and bounded measurable rewards, with an embedding $\phi:S\to\bar S$. Assume $\bar M$ is $(K_{\bar R},K_{\bar P})$-Lipschitz with $\gamma K_{\bar P}<1$ (Assumption 1). Let $\bar\pi$ be a $K_{\bar V}$-Lipschitz-valued policy on $\bar S$. Then for all $s\in S$ and $a\in A$,
--
--   $$\big|Q^{\bar\pi}(s,a)-\bar Q^{\bar\pi}(\phi(s),a)\big|\le\frac{L^\infty_{\bar R}+\gamma K_{\bar V}L^\infty_{\bar P}}{1-\gamma},$$
--
--   where $Q^{\bar\pi}$ is computed in $M$ for the policy $s\mapsto\bar\pi(\cdot|\phi(s))$ and $\bar Q^{\bar\pi}$ in $\bar M$.
--
--   Small global losses therefore make the DeepMDP's value functions accurate for every Lipschitz-valued latent policy.
--
--   **Formalization Note** Both sides are compared in $[0,\infty]$, with the convention $0\cdot\infty=0$. If $\gamma>0$ and $K_{\bar V}>0$, an infinite transition loss makes the bound trivially true. If $\gamma=0$ or $K_{\bar V}=0$, the term $\gamma K_{\bar V}L^\infty_{\bar P}$ is $0$ even when the loss is infinite, and the bound still holds. For $\gamma=0$ the transition plays no role. For $K_{\bar V}=0$, $\bar V^{\bar\pi}$ is constant, so its expectations under any two distributions agree. The proof does not use Assumption 1; it is included because the paper imposes it from Section 2.4 onwards.
-- source:
--   Gelada, Kumar, Buckman, Nachum and Bellemare, DeepMDP: Learning Continuous Latent Space Models for Representation Learning, arXiv:1906.02736v1 (ICML 2019), Section 3.1, Lemma 2, p. 4; proof via Lemma 7, Appendix A.6, p. 21

import Mathlib
import Definitions.Def_DeepMDP_Basic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace DeepMDP

theorem global_value_difference_bound {S Sb A : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    [MetricSpace Sb] [MeasurableSpace Sb] [BorelSpace Sb]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (R : S → A → ℝ) (P : A → Kernel S S) (Rb : Sb → A → ℝ) (Pb : A → Kernel Sb Sb) (γ : ℝ)
    (φ : S → Sb) (hM : IsMDP R P γ) (hMb : IsMDP Rb Pb γ)
    (KRb KPb : ℝ≥0) (hLip : IsLipschitzMDP Rb Pb KRb KPb) (hA1 : γ * (KPb : ℝ) < 1)
    (πb : Kernel Sb A) [IsMarkovKernel πb] (KV : ℝ≥0) (hπ : IsLipschitzValued Rb Pb γ πb KV)
    (s : S) (a : A) :
    ENNReal.ofReal |qValue R P γ (liftPolicy πb φ) s a - qValue Rb Pb γ πb (φ s) a| ≤
      (rewardLossGlobal R Rb φ + ENNReal.ofReal γ * (KV : ℝ≥0∞) * transLossGlobal P Pb φ) /
        ENNReal.ofReal (1 - γ) := by sorry

end DeepMDP
