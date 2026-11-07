-- Prove2me | Theorems.Thm_BertsekasShreve_ImperfectInfo_optCostHat_univMeasurable
-- name    : BertsekasShreve.ImperfectInfo.optCostHat_univMeasurable
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T05:23:58.251645+00:00
-- url     : https://prove2.me/theorems/852b7d87-506f-4947-a9d1-f03c4fb22a32
-- title:
--   Prop. 8.2 for (PSI) — the optimal cost $\hat J^*_N$ is universally measurable
-- statement:
--   Let an (ISI) model with finite horizon $N$ be given, together with a statistic $(\eta_0,\dots,\eta_{N-1})$ sufficient for control (Definition 10.6) and the associated perfect state information model (PSI) of Definition 10.7: states $Y_k$, control space $C$, constraint sets $\hat U_k(y_k)=(\hat\Gamma_k)_{y_k}$, one-stage costs $\hat g_k:\hat\Gamma_k\to\mathbb R^*$ and transition kernels $\hat t_k(dy_{k+1}\mid y_k,u_k)$. For a (PSI) policy $\hat\pi\in\hat\Pi'$ (universally measurable kernels $\hat\mu_k(du_k\mid y_0,u_0,\dots,y_k)$ with $\hat\mu_k(\hat U_k(y_k)\mid\cdot)=1$), $\hat J_{N,\hat\pi}(y)$ denotes its (0-originating) cost at $y\in Y_0$ (eq. (31)), and $\hat J^*_N(y)=\inf_{\hat\pi\in\hat\Pi'}\hat J_{N,\hat\pi}(y)$ is the optimal cost (eq. (32)).
--
--   If $(\hat F^+)$ or $(\hat F^-)$ holds for (PSI), then the optimal cost function
--
--   $$\hat J^*_N : Y_0\to\mathbb R^*$$
--
--   is universally measurable: for every probability measure $q$ on $Y_0$ it is measurable with respect to the $q$-completion of the Borel $\sigma$-algebra.
--
--   By Proposition 8.2, $\hat J^*_N=T^N(J_0)$, which is lower semianalytic (Lemma 7.30(4), Propositions 7.47 and 7.48), and lower semianalytic functions are universally measurable (Corollary 7.42.1). This is what gives meaning to the integral $\int_{Y_0}\hat J^*_N\,d\varphi(p)$ in Proposition 10.3 and to the notion of a $q$-optimal policy (Definition 10.8).
--
--   **Formalization Note** Universal measurability is `UnivMeasurable` of the Foundations definitions: null-measurability with respect to every probability measure on $Y_0$. The (PSI) model applies Chapter 8 through the nonstationary reduction of Section 10.1.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, Proposition 8.2 (p. 198) with Corollary 7.42.1, applied to the model (PSI) of Definition 10.7 (p. 251) as used in Proposition 10.3 (p. 256) and Definition 10.8

import Mathlib
import Definitions.Def_BertsekasShreve_ImperfectInfo_SufficientStatistic

open MeasureTheory ProbabilityTheory

namespace BertsekasShreve.ImperfectInfo

theorem optCostHat_univMeasurable {S C Z : Type}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (M : ISIModel S C Z) {Y : ℕ → Type} [∀ k, TopologicalSpace (Y k)] [∀ k, MeasurableSpace (Y k)]
    (σ : SuffStat M Y)
    (hF : σ.FhatPlus ∨ σ.FhatMinus) :
    UnivMeasurable σ.optCostHat := by sorry

end BertsekasShreve.ImperfectInfo
