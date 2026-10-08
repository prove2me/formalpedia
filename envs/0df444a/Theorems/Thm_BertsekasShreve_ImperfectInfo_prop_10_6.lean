-- Prove2me | Theorems.Thm_BertsekasShreve_ImperfectInfo_prop_10_6
-- name    : BertsekasShreve.ImperfectInfo.prop_10_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:03:57.082355+00:00
-- url     : https://prove2.me/theorems/b8cbed7b-d890-4a6d-9570-0949aef8e5eb
-- title:
--   Proposition 10.6 — the identity maps on $P(S)I_k$ are a statistic sufficient for control
-- statement:
--   Let an (ISI) model with finite horizon $N$ be given. Take $Y_k=P(S)I_k$ and let $\eta_k$ be the identity map on $P(S)I_k$, $k=0,\dots,N-1$. Then $(\eta_0,\dots,\eta_{N-1})$ is a statistic sufficient for control: there exist analytic sets $\hat\Gamma_k$, Borel kernels $\hat t_k$ and lower semianalytic functions $\hat g_k$ satisfying conditions (a), (b) and (c) of Definition 10.6.
--
--   Consequently every (ISI) model admits a statistic sufficient for control, so the reduction of Proposition 10.3 always applies.
--
--   **Formalization Note** $P(S)$ carries the weak topology and its Borel $\sigma$-algebra; $I_k$ the product topology. The statement asserts the existence of the whole structure of Definition 10.6 with $\eta_k=\mathrm{id}$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 264, Proposition 10.6

import Mathlib
import Definitions.Def_BertsekasShreve_ImperfectInfo_SufficientStatistic

open MeasureTheory ProbabilityTheory

namespace BertsekasShreve.ImperfectInfo

/-- Proposition 10.6 (p. 264). -/
theorem prop_10_6 {S C Z : Type}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (M : ISIModel S C Z) :
    ∃ σ : SuffStat M (fun k => ProbabilityMeasure S × Info Z C k), ∀ k, σ.η k = id := by sorry

end BertsekasShreve.ImperfectInfo
