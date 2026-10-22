-- Prove2me | Theorems.Thm_AnalystRank_Informativeness_proposition_5_B1
-- name    : AnalystRank.Informativeness.proposition_5_B1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:16.944474+00:00
-- url     : https://prove2.me/theorems/61ae79da-d9a4-4577-a45a-ff4f76d2af39
-- title:
--   Proposition 5 (B.1), corrected — for q ≥ 1/2, competition lowers informativeness iff φ > 1, ρ > 0 and q̌min < q ≤ γ
-- statement:
--   Two analysts forecast a binary state $\omega\in\{H,L\}$ with prior $\Pr(H)=q$, each from a private binary signal of precision $\gamma\in(\tfrac12,1)$. The signals are correlated given the state, with correlation $\rho\in[0,1]$. Under **competition** an analyst is paid $w_1$, $w_0$ or $w_2$ ($w_1>w_0>w_2$) when he is ranked high, tied or low in forecast accuracy, with payoff convexity $\varphi=(w_1-w_0)/(w_0-w_2)\neq1$. In the **benchmark** he is paid for his own accuracy only. For each game let $\sigma$ (resp. $\sigma_B$) be its most informative symmetric equilibrium, and let $\Pi$ be forecast informativeness (Definition 3). Put
--
--   $$\check q_{\min}=\gamma-\rho\gamma(1-\gamma)\,\frac{\varphi-1}{(1-\gamma)\varphi+\gamma}.$$
--
--   The theorem has two halves:
--
--   1. **(only if)** for every $q\in[\tfrac12,1)$, if $\sigma$ and $\sigma_B$ are most informative equilibria of the rank and benchmark games at $q$ and $\Pi(\sigma)<\Pi(\sigma_B)$, then
--   $$\varphi>1,\qquad \rho>0,\qquad \check q_{\min}<q\le\gamma ;$$
--   2. **(if)** if $\varphi>1$ and $\rho>0$, then for every $q$ with $q\ge\tfrac12$ and $\check q_{\min}<q\le\gamma$, both games have a most informative equilibrium at $q$, and every such pair satisfies $\Pi(\sigma)<\Pi(\sigma_B)$.
--
--   Competition among analysts therefore reduces the information their forecasts reveal exactly when the payoff is convex in rank, the signals are positively correlated and the prior uncertainty is high. Results for $q<\tfrac12$ are symmetric, as the paper notes.
--
--   **Formalization Note** *Corrected.* The paper prints "if and only if … $\varphi>1$, $\rho>0$ and $q<\gamma$". At $q=\gamma$ (with $\varphi>1$, $\rho>0$) the benchmark's most informative equilibrium is still $(1,1)$ while the rank game's is $(1,\check\sigma^l(\gamma))$ with $\check\sigma^l(\gamma)<1$. Informativeness therefore drops at $q=\gamma$ (e.g. $\gamma=0.7$, $\rho=0.4$, $\varphi=3$: $\Pi=0.147<\Pi_B=0.232$), and the printed "only if" is false there. For $q\in[\tfrac12,\check q_{\min}]$, $(1,1)$ is a rank-game equilibrium and $\Pi=\Pi_B$, so the printed "if" is false there. The interval $(\check q_{\min},\gamma]$ is the one in the paper's proof (p. 60) and discussion (p. 26). The restriction $q\ge\tfrac12$ is the paper's ("Proposition 5 summarizes results for $q\geqslant\frac12$"). The "Furthermore, the decrease … increases with payoff convexity" clause is not part of this statement. Both games' equilibria, and $\Pi$, are computed from the model's primitives.
-- source:
--   Banerjee, Does Competition Improve Analysts’ Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (13 Nov 2017), p. 25, Proposition 5 (B.1) (corrected: q ≤ γ, and the decrease holds on (q̌min, γ]; cf. pp. 26, 59–60)

import Mathlib
import Definitions.Def_AnalystRank_Informativeness_Model

namespace AnalystRank.Informativeness

open Set

theorem proposition_5_B1 (γ ρ w1 w0 w2 : ℝ) (hγ0 : 1 / 2 < γ) (hγ1 : γ < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hw1 : w0 < w1) (hw2 : w2 < w0) (hφ : phi w1 w0 w2 ≠ 1) :
    (∀ (q : ℝ) (σ σB : ℝ × ℝ), 1 / 2 ≤ q → q < 1 →
        IsMostInformative (rankEqSet w1 w0 w2 q γ ρ) σ →
        IsMostInformative (benchEqSet q γ ρ) σB →
        informativeness q γ ρ σ < informativeness q γ ρ σB →
        1 < phi w1 w0 w2 ∧ 0 < ρ ∧ qmin γ ρ (phi w1 w0 w2) < q ∧ q ≤ γ) ∧
    (1 < phi w1 w0 w2 → 0 < ρ → ∀ q : ℝ, 1 / 2 ≤ q → qmin γ ρ (phi w1 w0 w2) < q → q ≤ γ →
        (∃ σ : ℝ × ℝ, IsMostInformative (rankEqSet w1 w0 w2 q γ ρ) σ) ∧
        (∃ σB : ℝ × ℝ, IsMostInformative (benchEqSet q γ ρ) σB) ∧
        ∀ σ σB : ℝ × ℝ, IsMostInformative (rankEqSet w1 w0 w2 q γ ρ) σ →
          IsMostInformative (benchEqSet q γ ρ) σB →
          informativeness q γ ρ σ < informativeness q γ ρ σB) := by sorry

end AnalystRank.Informativeness
