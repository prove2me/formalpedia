-- Prove2me | Theorems.Thm_DeepMDP_norm_mmd_global_value_difference_bound
-- name    : DeepMDP.norm_mmd_global_value_difference_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:31:12.085253+00:00
-- url     : https://prove2.me/theorems/9981495d-4d21-4b72-9170-740db3e129a2
-- title:
--   Lemma 7: global value difference bound for Norm-MMD metrics
-- statement:
--   Let $M=\langle S,A,R,P,\gamma\rangle$ be an MDP with countable discrete state space and $\bar M=\langle\bar S,A,\bar R,\bar P,\gamma\rangle$ a DeepMDP on a measurable space $\bar S$, both with finite action set, discount $0\le\gamma<1$ and bounded measurable rewards, and let $\phi:S\to\bar S$. Let $D$ be a Norm-MMD with function seminorm $\|\cdot\|_D$ (possibly $+\infty$-valued), and let the global transition loss use $D$: $L^\infty_{\bar P}=\sup_{s,a}D(\phi P(\cdot|s,a),\bar P(\cdot|\phi(s),a))$. For every $K_{\bar V}$-smooth-valued policy $\bar\pi$ with $K_{\bar V}>0$ and all $s\in S$, $a\in A$,
--
--   $$\big|Q^{\bar\pi}(s,a)-\bar Q^{\bar\pi}(\phi(s),a)\big|\le\frac{L^\infty_{\bar R}+\gamma K_{\bar V}L^\infty_{\bar P}}{1-\gamma}.$$
--
--   This generalises Lemma 2 from the Wasserstein metric to Norm-MMD metrics such as the total variation and the energy distance.
--
--   **Formalization Note** The supremum defining an MMD ranges over the functions in the class that are integrable under both measures, so that both expectations exist. Both sides are compared in $[0,\infty]$, where $0\cdot\infty=0$. The hypothesis $K_{\bar V}>0$ is added for this reason. A seminorm may vanish on non-constant functions (the footnote to Section 6.1 allows this). If $\|\bar V^{\bar\pi}\|_D=0$, every multiple of $\bar V^{\bar\pi}$ lies in $F_D$, so the loss $L^\infty_{\bar P}$ can be $+\infty$. With $K_{\bar V}=0$ the term $\gamma K_{\bar V}L^\infty_{\bar P}$ would then be $0$ and the bound false. An example is the zero seminorm on two states with absorbing versus swapping transitions. The paper's real-valued $K_{\bar V}\cdot D$ is undefined in that case. The restriction loses nothing: a $0$-smooth-valued policy is $K$-smooth-valued for every $K>0$, and when the loss is finite, letting $K\to0$ recovers the $K_{\bar V}=0$ bound. Assumption 1 (a Lipschitz DeepMDP) is not imposed: Section 6.2 treats DeepMDPs under the total variation with bounded rewards only, and the proof does not use it.
-- source:
--   Gelada, Kumar, Buckman, Nachum and Bellemare, DeepMDP: Learning Continuous Latent Space Models for Representation Learning, arXiv:1906.02736v1 (ICML 2019), Section 6.3 and Appendix A.6, Lemma 7, p. 21; Definitions 6-7, pp. 7-8

import Mathlib
import Definitions.Def_DeepMDP_Basic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace DeepMDP

theorem norm_mmd_global_value_difference_bound {S Sb A : Type*} [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [Countable S] [MeasurableSpace Sb]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (R : S → A → ℝ) (P : A → Kernel S S) (Rb : Sb → A → ℝ) (Pb : A → Kernel Sb Sb) (γ : ℝ)
    (φ : S → Sb) (hM : IsMDP R P γ) (hMb : IsMDP Rb Pb γ) (sn : FunSeminorm Sb)
    (πb : Kernel Sb A) [IsMarkovKernel πb] (KV : ℝ≥0) (hπ : IsSmoothValued sn Rb Pb γ πb KV)
    (hKV : 0 < KV)
    (s : S) (a : A) :
    ENNReal.ofReal |qValue R P γ (liftPolicy πb φ) s a - qValue Rb Pb γ πb (φ s) a| ≤
      (rewardLossGlobal R Rb φ + ENNReal.ofReal γ * (KV : ℝ≥0∞) * transLossGlobalMMD sn P Pb φ) /
        ENNReal.ofReal (1 - γ) := by sorry

end DeepMDP
