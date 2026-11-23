-- Prove2me | Theorems.Thm_DeepMDP_bisimulation_metric_lipschitz
-- name    : DeepMDP.bisimulation_metric_lipschitz
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:31:47.179317+00:00
-- url     : https://prove2.me/theorems/aeb53460-7fa5-4b75-b8b4-d6f56395aa75
-- title:
--   Lemma 4: the bisimulation metric of a Lipschitz DeepMDP is Lipschitz
-- statement:
--   Let $\bar M=\langle\bar S,A,\bar R,\bar P,\gamma\rangle$ be a DeepMDP on a complete separable metric space $(\bar S,d_{\bar S})$ with finite action set, discount $0\le\gamma<1$ and bounded measurable rewards. Assume $\bar M$ is $(K_{\bar R},K_{\bar P})$-Lipschitz with $\gamma K_{\bar P}<1$ (Assumption 1). Then the bisimulation metric $\tilde d$ of $\bar M$ is Lipschitz: for all $\bar s_1,\bar s_2\in\bar S$,
--
--   $$\tilde d(\bar s_1,\bar s_2)\le\frac{(1-\gamma)K_{\bar R}}{1-\gamma K_{\bar P}}\,d_{\bar S}(\bar s_1,\bar s_2).$$
--
--   **Formalization Note** The bisimulation metric is the limit of the iterates $d_0=0$, $d_{n+1}=F(d_n)$ of Definition 5, as in the proof. The state space is taken Polish (complete and separable), the setting of Ferns et al. (2011) cited in Definition 5. The paper's statement says "$K_R$-$K_P$-Lipschitz" and its proof divides by $d_S$; both are typographical slips for $K_{\bar R}$, $K_{\bar P}$ and $d_{\bar S}$.
-- source:
--   Gelada, Kumar, Buckman, Nachum and Bellemare, DeepMDP: Learning Continuous Latent Space Models for Representation Learning, arXiv:1906.02736v1 (ICML 2019), Appendix A.4, Lemma 4, eq. (9), p. 18; Definition 5, Section 5.2, p. 6

import Mathlib
import Definitions.Def_DeepMDP_Basic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace DeepMDP

theorem bisimulation_metric_lipschitz {Sb A : Type*} [MetricSpace Sb] [MeasurableSpace Sb]
    [BorelSpace Sb] [SecondCountableTopology Sb] [CompleteSpace Sb]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (Rb : Sb → A → ℝ) (Pb : A → Kernel Sb Sb) (γ : ℝ) (hMb : IsMDP Rb Pb γ)
    (KRb KPb : ℝ≥0) (hLip : IsLipschitzMDP Rb Pb KRb KPb) (hA1 : γ * (KPb : ℝ) < 1) (x y : Sb) :
    bisimMetric Rb (fun x a => Pb a x) γ x y ≤
      ENNReal.ofReal ((1 - γ) * KRb / (1 - γ * KPb)) * edist x y := by sorry

end DeepMDP
