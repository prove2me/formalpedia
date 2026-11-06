-- Prove2me | Theorems.Thm_BilateralProfit_running_time
-- name    : BilateralProfit.running_time
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:22:18.304529+00:00
-- url     : https://prove2.me/theorems/d888a90e-be08-4b7d-84a1-4089d60542e6
-- title:
--   §4.2.2 (proof of Theorem 4.1) — the algorithm runs in time $\tilde O(TK^{12})$
-- statement:
--   There are constants $C$ and $c$ such that for every horizon $T\ge1$, every resolution $K\ge1$, every valuation sequence in $[0,1]^2$ and every realization of the randomness, Algorithm 1 performs at most
--   $$C\,T\,K^{12}\,(1+\log K)^c$$
--   unit-cost operations.
--
--   Each OneRound iteration scans $\mathcal A$ and, for each candidate, $G_K\times\mathcal A$, which is $O(K^6)$; with $J$ iterations at most and one OneRound call per round this is the paper's crude $\tilde O(TK^{12})$ bound. With $K=K(T)$ it gives the polynomial-time clause of Theorem 4.1.
--
--   **Formalization Note** The operation count is the counter of the run itself (unit-cost real arithmetic, logarithms, comparisons, table reads and writes, loop steps). Bit complexity is not claimed.
--
--   Differences from the source:
--   - encoding: "runs in polynomial time … a crude $\tilde O(TK^{12})$ bound" → $\exists C,c$: the run's unit-cost operation count is at most $C\,T\,K^{12}(1+\log K)^c$ for all $T\ge1$, $K\ge1$; reason: $\tilde O$ hides a polylogarithmic factor; the paper counts operations of real arithmetic (p.23)
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), proof of Theorem 4.1, §4.2.2, p.23 (PDF 25)

import Mathlib
import Definitions.Def_BilateralProfit_Algorithm1

namespace BilateralProfit

/-- **The running time of Algorithm 1**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript,
sha256 e91e8127…), §4.2.2, p.23 (PDF 25): each OneRound iteration costs `O(K⁶)`, and with the
values of `J` and `H` and one OneRound call per round, the algorithm runs in `Õ(TK^12)` time.

There are constants `C, c` such that for every horizon `T ≥ 1`, resolution `K ≥ 1`, valuation
sequence in `[0,1]²` and realization of the randomness, the run of Algorithm 1 performs at most
`C · T · K^12 · (1 + log K)^c` unit-cost operations.

**Formalization Note.** `Õ(·)` hides a power of `1 + log K`. The cost model is that of
`OneRound`: the counter of the run itself. -/
theorem running_time :
    ∃ C c : ℝ, ∀ T K : ℕ, 1 ≤ T → 1 ≤ K →
      ∀ S : Fin T → ℝ × ℝ, (∀ t, S t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) →
        ∀ ω : Fin T → Fin (Jpar K),
          (alg1Cost K T S ω : ℝ) ≤ C * T * (K : ℝ) ^ 12 * (1 + Real.log K) ^ c := by sorry

end BilateralProfit
