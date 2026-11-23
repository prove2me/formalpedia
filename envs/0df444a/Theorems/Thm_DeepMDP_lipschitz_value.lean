-- Prove2me | Theorems.Thm_DeepMDP_lipschitz_value
-- name    : DeepMDP.lipschitz_value
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:27:10.40803+00:00
-- url     : https://prove2.me/theorems/f2c98c8f-3185-4741-a690-a8c987b43336
-- title:
--   Lemma 1: Lipschitz-valued policies (part 2 as proved)
-- statement:
--   Let $\bar M$ be a $(K_{\bar R},K_{\bar P})$-Lipschitz DeepMDP with discount $0\le\gamma<1$, bounded measurable rewards, and $\gamma K_{\bar P}<1$ (Assumption 1). Then:
--
--   1. Every optimal policy $\bar\pi^*$ of $\bar M$ is $\dfrac{K_{\bar R}}{1-\gamma K_{\bar P}}$-Lipschitz-valued.
--   2. Let $\bar\pi$ be a policy whose reward function $\bar R_{\bar\pi}$ is $K_{\bar R_{\bar\pi}}$-Lipschitz and whose transition function satisfies $W(\bar P_{\bar\pi}(\cdot|\bar s_1),\bar P_{\bar\pi}(\cdot|\bar s_2))\le K_{\bar P_{\bar\pi}}\,d_{\bar S}(\bar s_1,\bar s_2)$, with $\gamma K_{\bar P_{\bar\pi}}<1$. Then $\bar V^{\bar\pi}$ is $\dfrac{K_{\bar R_{\bar\pi}}}{1-\gamma K_{\bar P_{\bar\pi}}}$-Lipschitz, and each $\bar Q^{\bar\pi}(\cdot,a)$ is Lipschitz.
--   3. Every constant policy ($\bar\pi(a|\bar s_1)=\bar\pi(a|\bar s_2)$ for all $a,\bar s_1,\bar s_2$) is $\dfrac{K_{\bar R}}{1-\gamma K_{\bar P}}$-Lipschitz-valued.
--
--   These are the policies to which the value-difference and representation bounds apply.
--
--   **Formalization Note** Part 2 is stated as the proof in Appendix A.1 establishes it. The printed part 2 claims that $\bar\pi$ is $K_{\bar R_{\bar\pi}}/(1-\gamma K_{\bar P_{\bar\pi}})$-Lipschitz-valued under $K_{\bar P_{\bar\pi}}\le1/\gamma$. That fails for $\bar Q^{\bar\pi}$, whose Lipschitz constant depends on the per-action rewards (see the mission report), and the constant is undefined when $\gamma K_{\bar P_{\bar\pi}}=1$. The proof shows the bound for $\bar V^{\bar\pi}$ under $\gamma K_{\bar P_{\bar\pi}}<1$ and states that $\bar Q^{\bar\pi}$ is also Lipschitz. The Lipschitz constant is passed to Lean's `LipschitzWith` as a nonnegative real.
-- source:
--   Gelada, Kumar, Buckman, Nachum and Bellemare, DeepMDP: Learning Continuous Latent Space Models for Representation Learning, arXiv:1906.02736v1 (ICML 2019), Section 2.4, Lemma 1, p. 4; proof in Appendix A.1, p. 16

import Mathlib
import Definitions.Def_DeepMDP_Basic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace DeepMDP

theorem lipschitz_value {Sb A : Type*} [MetricSpace Sb] [MeasurableSpace Sb] [BorelSpace Sb]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (Rb : Sb → A → ℝ) (Pb : A → Kernel Sb Sb) (γ : ℝ) (hMb : IsMDP Rb Pb γ)
    (KRb KPb : ℝ≥0) (hLip : IsLipschitzMDP Rb Pb KRb KPb) (hA1 : γ * (KPb : ℝ) < 1) :
    (∀ πs : Kernel Sb A, IsOptimalPolicy Rb Pb γ πs →
      IsLipschitzValued Rb Pb γ πs (Real.toNNReal (KRb / (1 - γ * KPb)))) ∧
    (∀ πb : Kernel Sb A, IsMarkovKernel πb → ∀ KRpi KPpi : ℝ≥0,
      LipschitzWith KRpi (policyReward Rb πb) →
      (∀ x y, wasserstein (policyTrans Pb πb x) (policyTrans Pb πb y) ≤ (KPpi : ℝ≥0∞) * edist x y) →
      γ * (KPpi : ℝ) < 1 →
      LipschitzWith (Real.toNNReal (KRpi / (1 - γ * KPpi))) (vValue Rb Pb γ πb) ∧
        ∀ a, ∃ K : ℝ≥0, LipschitzWith K fun x => qValue Rb Pb γ πb x a) ∧
    (∀ πb : Kernel Sb A, IsMarkovKernel πb → (∀ a x y, πb x {a} = πb y {a}) →
      IsLipschitzValued Rb Pb γ πb (Real.toNNReal (KRb / (1 - γ * KPb)))) := by sorry

end DeepMDP
