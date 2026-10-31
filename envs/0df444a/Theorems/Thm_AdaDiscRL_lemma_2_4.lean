-- Prove2me | Theorems.Thm_AdaDiscRL_lemma_2_4
-- name    : AdaDiscRL.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:34.700918+00:00
-- url     : https://prove2.me/theorems/e36a2044-3fb8-4436-ac7f-914604b38a73
-- title:
--   Lemma 2.4 — Assumption 2 implies Assumption 1 with $L_V=\sum_{h=0}^H L_rL_T^h$
-- statement:
--   Let $\mathcal S,\mathcal A$ be compact metric spaces, $\mathcal D$ a metric on $\mathcal S\times\mathcal A$ with $\mathcal D\le\mathcal D_{\mathcal S}+\mathcal D_{\mathcal A}$, and $M$ an episodic MDP with horizon $H$. If $M$ satisfies Assumption 2 with constants $L_r,L_T\ge0$ (Lipschitz mean rewards, Wasserstein-Lipschitz transitions), then it satisfies Assumption 1 with
--   $$
--   L_V=\sum_{h=0}^{H}L_rL_T^h ,
--   $$
--   that is, every $Q^\star_h$ is $L_V$-Lipschitz in $\mathcal D$ and every $V^\star_h$ is $L_V$-Lipschitz in $\mathcal D_{\mathcal S}$.
--
--   This is why AdaMB, analysed under Assumption 2, may use the model-free constant $L_V$ in its bonuses.
--
--   Differences from the source:
--   - encoding: Lipschitz constants L_r, L_T → 0 ≤ L_r, 0 ≤ L_T; reason: Lipschitz constants are nonnegative by convention
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Lemma 2.4, p.10 (= Lemma J.4, p.67)

import Mathlib
import Definitions.Def_AdaDiscRL_Assumption1
import Definitions.Def_AdaDiscRL_Assumption2
import Definitions.Def_AdaDiscRL_IsAdmissibleMetric

open MeasureTheory ProbabilityTheory Classical

namespace AdaDiscRL

/-- **Lemma 2.4** (arXiv:2110.15843v3, p.10; = Lemma J.4, p.67). If Assumption 2 holds with constants
`L_r, L_T`, then Assumption 1 holds with `L_V = Σ_{h=0}^{H} L_r L_T^h`.

**Formalization Note.** Lipschitz constants are nonnegative. `D` is any metric on `S × A` with
`D ≤ D_S + D_A` (p.10). -/
theorem lemma_2_4 {S A ι : Type} [MetricSpace S] [CompactSpace S] [Nonempty S] [MeasurableSpace S]
    [BorelSpace S] [MetricSpace A] [CompactSpace A] [Nonempty A] [MeasurableSpace A]
    [BorelSpace A]
    {H : ℕ} (M : EpisodicMDP S A H) (D : S × A → S × A → ℝ) (Lr LT : ℝ)
    (hD : IsAdmissibleMetric D) (hLr : 0 ≤ Lr) (hLT : 0 ≤ LT) (h2 : Assumption2 M D Lr LT) :
    Assumption1 M D (∑ i ∈ Finset.range (H + 1), Lr * LT ^ i) := by sorry

end AdaDiscRL
