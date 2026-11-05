-- Prove2me | Theorems.Thm_BauerleRiederMDP_NoArbitrage_theorem_3_1_5
-- name    : BauerleRiederMDP.NoArbitrage.theorem_3_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:28:56.071367+00:00
-- url     : https://prove2.me/theorems/81ab80ad-2365-420b-b2a3-f06aa3939ec3
-- title:
--   Theorem 3.1.5 — no arbitrage iff no local arbitrage
-- statement:
--   Consider an $N$-period financial market. The following statements are equivalent:
--
--   1. there are no arbitrage opportunities;
--   2. for $n=0,1,\dots,N-1$ and every $\mathcal F_n$-measurable $\varphi_n\in\mathbb R^d$,
--   $$
--   \varphi_n\cdot R_{n+1}\ge0\ \ \mathbb P\text{-a.s.}\quad\Longrightarrow\quad\varphi_n\cdot R_{n+1}=0\ \ \mathbb P\text{-a.s.}
--   $$
--
--   The market is free of arbitrage if and only if there is no arbitrage in any single period; this reduces multiperiod problems to one-period ones.
--
--   Differences from the source:
--   - encoding: the $N$-period market of §3.1 on $(\Omega,\mathcal F,(\mathcal F_n),\mathbb P)$ with $\mathbb R^d$, time $n=0,\dots,N$ and $x\cdot y=\sum_k x_ky_k$ → `FinancialMarket`: data indexed by $n\in\mathbb N$ and constrained only for the times the book uses, $\mathbb R^d$ as `Fin d → ℝ`, inner products as finite sums; reason: the values at unused times never enter a statement; same objects
--   - reading: deterministic initial prices $s^k_0$, adapted prices $S^k_n$, $\tilde R^k_{n+1}>0$ a.s. → in addition $s^k_0>0$ and each $\tilde R_n$ is $\mathcal F$-measurable; reason: p.61 calls $\tilde R_n$ random variables on $(\Omega,\mathcal F,\mathbb P)$ and says the stock price stays positive, so these are the book's own standing assumptions made explicit
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 3.1.5, p.64 (PDF 78)

import Mathlib
import Definitions.Def_BauerleRiederMDP_NoArbitrage_FinancialMarket_relRisk
import Definitions.Def_BauerleRiederMDP_NoArbitrage_FinancialMarket_ArbitrageFree

open MeasureTheory

namespace BauerleRiederMDP.NoArbitrage

/-- Theorem 3.1.5 (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance
(2011), Theorem 3.1.5, p.64, PDF 78): in an `N`-period financial market the following two
statements are equivalent:
a) there are no arbitrage opportunities;
b) for `n = 0, 1, …, N − 1` and for all `𝓕_n`-measurable `φ_n ∈ ℝ^d` it holds:
`φ_n · R_{n+1} ≥ 0` `ℙ`-a.s. `⇒` `φ_n · R_{n+1} = 0` `ℙ`-a.s. -/
theorem theorem_3_1_5 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (M : FinancialMarket Ω P d) :
    M.ArbitrageFree ↔
      ∀ n, n < M.N → ∀ ψ : Ω → Fin d → ℝ, Measurable[M.F n] ψ →
        (∀ᵐ ω ∂P, 0 ≤ ∑ k, ψ ω k * M.relRisk (n + 1) ω k) →
          ∀ᵐ ω ∂P, ∑ k, ψ ω k * M.relRisk (n + 1) ω k = 0 := by sorry

end BauerleRiederMDP.NoArbitrage
