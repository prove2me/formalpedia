-- Prove2me | Theorems.Thm_BauerleRiederMDP_NoArbitrage_eq_3_1
-- name    : BauerleRiederMDP.NoArbitrage.eq_3_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:26:38.957183+00:00
-- url     : https://prove2.me/theorems/826400bb-9975-4a2e-a555-931a16f0229b
-- title:
--   Eq. (3.1) — wealth recursion of a self-financing strategy
-- statement:
--   Let $\varphi$ be a self-financing portfolio strategy in an $N$-period financial market, with wealth $X_n=X^\varphi_n$ and relative risk process $R_n$. Then for $n=0,\dots,N-1$,
--   $$
--   X_{n+1}=(1+i_{n+1})\bigl(X_n+\varphi_n\cdot R_{n+1}\bigr)\qquad\mathbb P\text{-a.s.} \tag{3.1}
--   $$
--   Only the investment in the stocks enters the recursion; it is the transition function of every portfolio Markov decision model in the book.
--
--   Differences from the source:
--   - encoding: the $N$-period market of §3.1 on $(\Omega,\mathcal F,(\mathcal F_n),\mathbb P)$ with $\mathbb R^d$, time $n=0,\dots,N$ and $x\cdot y=\sum_k x_ky_k$ → `FinancialMarket`: data indexed by $n\in\mathbb N$ and constrained only for the times the book uses, $\mathbb R^d$ as `Fin d → ℝ`, inner products as finite sums; reason: the values at unused times never enter a statement; same objects
--   - reading: deterministic initial prices $s^k_0$, adapted prices $S^k_n$, $\tilde R^k_{n+1}>0$ a.s. → in addition $s^k_0>0$ and each $\tilde R_n$ is $\mathcal F$-measurable; reason: p.61 calls $\tilde R_n$ random variables on $(\Omega,\mathcal F,\mathbb P)$ and says the stock price stays positive, so these are the book's own standing assumptions made explicit
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (3.1), p.63 (PDF 77)

import Mathlib
import Definitions.Def_BauerleRiederMDP_NoArbitrage_FinancialMarket_relRisk
import Definitions.Def_BauerleRiederMDP_NoArbitrage_Portfolio_IsSelfFinancing

open MeasureTheory

namespace BauerleRiederMDP.NoArbitrage

/-- Equation (3.1) (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance
(2011), eq. (3.1), p.63, PDF 77): the wealth of a self-financing portfolio strategy satisfies
`X_{n+1} = (1 + i_{n+1})(X_n + φ_n · R_{n+1})` `ℙ`-a.s. for `n = 0, …, N − 1`, where
`R^k_n = R̃^k_n / (1 + i_n) − 1` is the relative risk process.

**Formalization Note** For `n ≥ 1` the identity uses the self-financing condition, which holds
`ℙ`-a.s., hence the a.s. conclusion. -/
theorem eq_3_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}
    (M : FinancialMarket Ω P d) (φ : Portfolio M) (hφ : φ.IsSelfFinancing) :
    ∀ n, n < M.N → ∀ᵐ ω ∂P,
      φ.wealth (n + 1) ω = (1 + M.i (n + 1)) * (φ.wealth n ω + ∑ k, φ.φ n ω k * M.relRisk (n + 1) ω k) := by sorry

end BauerleRiederMDP.NoArbitrage
