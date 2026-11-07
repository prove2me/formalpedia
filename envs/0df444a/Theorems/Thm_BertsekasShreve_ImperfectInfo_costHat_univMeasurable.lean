-- Prove2me | Theorems.Thm_BertsekasShreve_ImperfectInfo_costHat_univMeasurable
-- name    : BertsekasShreve.ImperfectInfo.costHat_univMeasurable
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T05:23:56.99683+00:00
-- url     : https://prove2.me/theorems/9f04a92f-c2ac-4a6a-9111-e92fab2e0c89
-- title:
--   (PSI) policy costs $\hat J_{N,\hat\pi}$ are universally measurable
-- statement:
--   Let an (ISI) model with finite horizon $N$ be given, together with a statistic $(\eta_0,\dots,\eta_{N-1})$ sufficient for control (Definition 10.6) and the associated perfect state information model (PSI) of Definition 10.7: states $Y_k$, control space $C$, constraint sets $\hat U_k(y_k)=(\hat\Gamma_k)_{y_k}$, one-stage costs $\hat g_k:\hat\Gamma_k\to\mathbb R^*$ and transition kernels $\hat t_k(dy_{k+1}\mid y_k,u_k)$. For a (PSI) policy $\hat\pi\in\hat\Pi'$ (universally measurable kernels $\hat\mu_k(du_k\mid y_0,u_0,\dots,y_k)$ with $\hat\mu_k(\hat U_k(y_k)\mid\cdot)=1$), $\hat J_{N,\hat\pi}(y)$ denotes its (0-originating) cost at $y\in Y_0$ (eq. (31)), and $\hat J^*_N(y)=\inf_{\hat\pi\in\hat\Pi'}\hat J_{N,\hat\pi}(y)$ is the optimal cost (eq. (32)).
--
--   If $(\hat F^+)$ or $(\hat F^-)$ holds for (PSI), then for every policy $\hat\pi\in\hat\Pi'$ the cost function
--
--   $$y\mapsto\hat J_{N,\hat\pi}(y)=\sum_{k=0}^{N-1}\alpha^k\int\hat g_k(y_k,u_k)\,d\hat P_k(\hat\pi,p_y)$$
--
--   is universally measurable on $Y_0$.
--
--   This is the remark following Definition 8.3 ("$J_{K,\pi}(x)$ is universally measurable in $x$", a consequence of Proposition 7.46), applied to the model (PSI). It is needed to integrate $\hat J_{N,\hat\pi}$ against $\varphi(p)$ in Propositions 10.2 and 10.3 and to evaluate the set $\{y_0\mid\hat J_{N,\hat\pi}(y_0)=\hat J^*_N(y_0)\}$ in the definition of $q$-optimality.
--
--   **Formalization Note** $\hat J_{N,\hat\pi}$ is `σ.costHat μ` (the stage-wise sum (31) with the convention $\infty-\infty=+\infty$); universal measurability is `UnivMeasurable`.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 191 (remark after Definition 8.3: J_{K,pi} universally measurable, via Proposition 7.46), applied to the (PSI) cost (31) on p. 254

import Mathlib
import Definitions.Def_BertsekasShreve_ImperfectInfo_SufficientStatistic

open MeasureTheory ProbabilityTheory

namespace BertsekasShreve.ImperfectInfo

theorem costHat_univMeasurable {S C Z : Type}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (M : ISIModel S C Z) {Y : ℕ → Type} [∀ k, TopologicalSpace (Y k)] [∀ k, MeasurableSpace (Y k)]
    (σ : SuffStat M Y)
    (hF : σ.FhatPlus ∨ σ.FhatMinus)
    (μ : (n : ℕ) → Obs Y C n → ProbabilityMeasure C) (hμ : σ.IsPolicy μ) :
    UnivMeasurable (σ.costHat μ) := by sorry

end BertsekasShreve.ImperfectInfo
