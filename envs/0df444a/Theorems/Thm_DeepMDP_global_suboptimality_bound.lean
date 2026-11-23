-- Prove2me | Theorems.Thm_DeepMDP_global_suboptimality_bound
-- name    : DeepMDP.global_suboptimality_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:30:40.445852+00:00
-- url     : https://prove2.me/theorems/05a08d27-2aef-490e-bd08-33f7043c7dcc
-- title:
--   Theorem 5: global suboptimality bound
-- statement:
--   Let $M$, $\bar M$ and $\phi$ be as in Lemma 2, with $\bar M$ $(K_{\bar R},K_{\bar P})$-Lipschitz and $\gamma K_{\bar P}<1$ (Assumption 1). Let $\bar\pi^*$ be an optimal policy of $\bar M$, and let $V^*(s)=\sup_\pi V^\pi(s)$ be the optimal value function of $M$. Then for all $s\in S$,
--
--   $$V^*(s)-V^{\bar\pi^*}(s)\le\frac{2L^\infty_{\bar R}}{1-\gamma}+\frac{2\gamma K_{\bar R}L^\infty_{\bar P}}{(1-\gamma)(1-\gamma K_{\bar P})},$$
--
--   where $V^{\bar\pi^*}$ is the value in $M$ of the policy $s\mapsto\bar\pi^*(\cdot|\phi(s))$.
--
--   The optimal policy of the DeepMDP is thus near-optimal in the original MDP when the global losses are small.
--
--   **Formalization Note** The comparison is made in $[0,\infty]$: the left side is the positive part of $V^*(s)-V^{\bar\pi^*}(s)$, which is nonnegative anyway.
-- source:
--   Gelada, Kumar, Buckman, Nachum and Bellemare, DeepMDP: Learning Continuous Latent Space Models for Representation Learning, arXiv:1906.02736v1 (ICML 2019), Section 3.3 and Appendix A.2, Theorem 5, p. 17; proof via Theorem 6, Appendix A.6, p. 22

import Mathlib
import Definitions.Def_DeepMDP_Basic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace DeepMDP

theorem global_suboptimality_bound {S Sb A : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    [MetricSpace Sb] [MeasurableSpace Sb] [BorelSpace Sb]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (R : S → A → ℝ) (P : A → Kernel S S) (Rb : Sb → A → ℝ) (Pb : A → Kernel Sb Sb) (γ : ℝ)
    (φ : S → Sb) (hM : IsMDP R P γ) (hMb : IsMDP Rb Pb γ)
    (KRb KPb : ℝ≥0) (hLip : IsLipschitzMDP Rb Pb KRb KPb) (hA1 : γ * (KPb : ℝ) < 1)
    (πs : Kernel Sb A) (hopt : IsOptimalPolicy Rb Pb γ πs) (s : S) :
    ENNReal.ofReal (optValue R P γ s - vValue R P γ (liftPolicy πs φ) s) ≤
      2 * rewardLossGlobal R Rb φ / ENNReal.ofReal (1 - γ) +
        2 * ENNReal.ofReal γ * (KRb : ℝ≥0∞) * transLossGlobal P Pb φ /
          (ENNReal.ofReal (1 - γ) * ENNReal.ofReal (1 - γ * KPb)) := by sorry

end DeepMDP
