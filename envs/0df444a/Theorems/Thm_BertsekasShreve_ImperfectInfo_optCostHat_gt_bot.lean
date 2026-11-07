-- Prove2me | Theorems.Thm_BertsekasShreve_ImperfectInfo_optCostHat_gt_bot
-- name    : BertsekasShreve.ImperfectInfo.optCostHat_gt_bot
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T05:23:56.690081+00:00
-- url     : https://prove2.me/theorems/6da73e4d-df90-4a51-98c7-0e0097e3ed86
-- title:
--   Eq. (10.42) — under $(\hat F^+)$ the (PSI) optimal cost is $>-\infty$
-- statement:
--   Let an (ISI) model with finite horizon $N$ be given, together with a statistic $(\eta_0,\dots,\eta_{N-1})$ sufficient for control (Definition 10.6) and the associated perfect state information model (PSI) of Definition 10.7: states $Y_k$, control space $C$, constraint sets $\hat U_k(y_k)=(\hat\Gamma_k)_{y_k}$, one-stage costs $\hat g_k:\hat\Gamma_k\to\mathbb R^*$ and transition kernels $\hat t_k(dy_{k+1}\mid y_k,u_k)$. For a (PSI) policy $\hat\pi\in\hat\Pi'$ (universally measurable kernels $\hat\mu_k(du_k\mid y_0,u_0,\dots,y_k)$ with $\hat\mu_k(\hat U_k(y_k)\mid\cdot)=1$), $\hat J_{N,\hat\pi}(y)$ denotes its (0-originating) cost at $y\in Y_0$ (eq. (31)), and $\hat J^*_N(y)=\inf_{\hat\pi\in\hat\Pi'}\hat J_{N,\hat\pi}(y)$ is the optimal cost (eq. (32)).
--
--   If assumption $(\hat F^+)$ holds for (PSI), i.e. $\int \hat g_j^-\,d\hat q_j(\hat\pi^k,p_{y_k})<\infty$ for all $k$-originating policies, all $y_k\in Y_k$ and $k\le j\le N-1$, then
--
--   $$\hat J^*_N(y_0)>-\infty\qquad\forall\,y_0\in Y_0.$$
--
--   This is equation (42) in the proof of Proposition 10.3; it is Lemma 8.3 combined with Proposition 8.2 ($J^*_N=T^N(J_0)$) applied to the model (PSI). It is what makes an $\varepsilon$-optimal (PSI) policy satisfy $\hat J_{N,\hat\pi}\le\hat J^*_N+\varepsilon$ everywhere.
--
--   **Formalization Note** The model (PSI) is the one bundled in `SuffStat` (Definitions 10.6–10.8); $\hat J^*_N$ is `σ.optCostHat`.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 257, eq. (42) in the proof of Proposition 10.3 (citing Lemma 8.3, p. 196, and Proposition 8.2, p. 198)

import Mathlib
import Definitions.Def_BertsekasShreve_ImperfectInfo_SufficientStatistic

open MeasureTheory ProbabilityTheory

namespace BertsekasShreve.ImperfectInfo

theorem optCostHat_gt_bot {S C Z : Type}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (M : ISIModel S C Z) {Y : ℕ → Type} [∀ k, TopologicalSpace (Y k)] [∀ k, MeasurableSpace (Y k)]
    (σ : SuffStat M Y)
    (hF : σ.FhatPlus) (y : Y 0) :
    ⊥ < σ.optCostHat y := by sorry

end BertsekasShreve.ImperfectInfo
