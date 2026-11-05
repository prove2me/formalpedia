-- Prove2me | Theorems.Thm_BauerleRiederMDP_NoArbitrage_theorem_C_1_2
-- name    : BauerleRiederMDP.NoArbitrage.theorem_C_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:28:48.886199+00:00
-- url     : https://prove2.me/theorems/49d87859-8e4a-460c-98b4-616a0100a354
-- title:
--   Theorem C.1.2 — fundamental theorem of asset pricing
-- statement:
--   Consider an $N$-period financial market. A probability measure $Q$ on $(\Omega,\mathcal F)$ is **equivalent** to $\mathbb P$ if $Q$ and $\mathbb P$ have the same null sets; it is a **martingale measure** if the discounted price processes $(S^k_n/S^0_n)_{n=0,\dots,N}$ are $(\mathcal F_n)$-martingales under $Q$ for all $k=1,\dots,d$. Then:
--
--   $$
--   \text{the market is free of arbitrage}\iff\text{there exists an equivalent martingale measure.}
--   $$
--
--   This is the Dalang–Morton–Willinger theorem in the setting of §3.1; the book cites it from Föllmer and Schied and uses it for pricing contingent claims.
--
--   **Formalization Note** The discounted price process is extended to all $n\in\mathbb N$ as constant after $N$, so Mathlib's martingale over $\mathbb N$ is the martingale property on $\{0,\dots,N\}$; integrability under $Q$ is part of the martingale property.
--
--   Differences from the source:
--   - encoding: the $N$-period market of §3.1 on $(\Omega,\mathcal F,(\mathcal F_n),\mathbb P)$ with $\mathbb R^d$, time $n=0,\dots,N$ and $x\cdot y=\sum_k x_ky_k$ → `FinancialMarket`: data indexed by $n\in\mathbb N$ and constrained only for the times the book uses, $\mathbb R^d$ as `Fin d → ℝ`, inner products as finite sums; reason: the values at unused times never enter a statement; same objects
--   - reading: deterministic initial prices $s^k_0$, adapted prices $S^k_n$, $\tilde R^k_{n+1}>0$ a.s. → in addition $s^k_0>0$ and each $\tilde R_n$ is $\mathcal F$-measurable; reason: p.61 calls $\tilde R_n$ random variables on $(\Omega,\mathcal F,\mathbb P)$ and says the stock price stays positive, so these are the book's own standing assumptions made explicit
--   - encoding: $Q$ equivalent to $\mathbb P$ on $(\Omega,\mathcal F)$ and a martingale measure on $(\Omega,\mathcal F_N)$; martingales indexed by $n=0,\dots,N$ → one probability measure $Q$ on $\mathcal F$ with $Q\ll\mathbb P$, $\mathbb P\ll Q$, and `Martingale` of $n\mapsto S^k_{\min(n,N)}/S^0_{\min(n,N)}$; reason: a measure on $\mathcal F$ restricts to $\mathcal F_N$, and one equivalent on $\mathcal F_N$ extends to $\mathcal F$ by its density; the stopped process is a martingale iff the original one is on $\{0,\dots,N\}$
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition C.1.1 and Theorem C.1.2, p.365 (PDF 370); Remark 3.1.8, p.65 (PDF 79)

import Mathlib
import Definitions.Def_BauerleRiederMDP_NoArbitrage_FinancialMarket_price
import Definitions.Def_BauerleRiederMDP_NoArbitrage_FinancialMarket_bondPrice
import Definitions.Def_BauerleRiederMDP_NoArbitrage_FinancialMarket_ArbitrageFree

open MeasureTheory

namespace BauerleRiederMDP.NoArbitrage

/-- Theorem C.1.2 (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance
(2011), Theorem C.1.2 with Definition C.1.1, p.365, PDF 370; the fundamental theorem of asset
pricing, cited from Föllmer–Schied): the financial market is free of arbitrage if and only if
there exists an equivalent martingale measure, i.e. a probability measure `Q` on `(Ω, 𝓕)` with the
same null sets as `ℙ` under which the discounted price processes `(S^k_n / S^0_n)` are
`(𝓕_n)`-martingales for all `k = 1, …, d`.

**Formalization Note** "Same null sets" is `Q ≪ ℙ ∧ ℙ ≪ Q`. The discounted price process lives on
`n = 0, …, N`; it is extended to all `n ∈ ℕ` as constant after `N` (`S^k_{min(n,N)} / S^0_{min(n,N)}`),
so Mathlib's `Martingale` over `ℕ` is the book's martingale property on `{0, …, N}`. Mathlib's
`Martingale` includes adaptedness and (through the conditional expectations) `Q`-integrability. -/
theorem theorem_C_1_2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (M : FinancialMarket Ω P d) :
    M.ArbitrageFree ↔
      ∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q ∧
        ∀ k : Fin d,
          Martingale (fun n ω => M.price (min n M.N) ω k / M.bondPrice (min n M.N)) M.F Q := by sorry

end BauerleRiederMDP.NoArbitrage
