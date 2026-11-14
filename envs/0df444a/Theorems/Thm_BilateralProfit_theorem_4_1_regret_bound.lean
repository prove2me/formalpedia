-- Prove2me | Theorems.Thm_BilateralProfit_theorem_4_1_regret_bound
-- name    : BilateralProfit.theorem_4_1_regret_bound
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T02:22:55.566734+00:00
-- url     : https://prove2.me/theorems/d08cf74d-f742-4708-9c47-98f98a275144
-- title:
--   Theorem 4.1 — a polynomial-time algorithm with regret $O(T^{2/3}\log^{7/3}T)$ against every oblivious adversary
-- statement:
--   There is a polynomial time algorithm $\mathcal A$ such that, for every valuation sequence $\mathcal S$ fixed in advance, the prices it posts satisfy
--   $$R_T(\mathcal A,\mathcal S)=\sup_{(p,q)\in[0,1]^2}\sum_{t=1}^T\mathbb E\big[\mathrm{Profit}_t(p,q)-\mathrm{Profit}_t(p_t,q_t)\big]\le O\big(T^{2/3}\log^{7/3}T\big).$$
--
--   Precisely: Algorithm 1 (with OneRound, eqs. (5), (6), (8)) at resolution $K(T)=\max(2,\lceil (T/\log^7T)^{1/3}\rceil)$ satisfies, for constants $C>0$ and $c$:
--
--   1. for every horizon $T\ge2$, every sequence $(s_1,b_1),\dots,(s_T,b_T)\in[0,1]^2$ and every comparator $(p,q)\in[0,1]^2$,
--   $$\sum_{t=1}^T\Big(\mathrm{Profit}_t(p,q)-\mathbb E\big[\mathrm{Profit}_t(p_t,q_t)\big]\Big)\le C\,T^{2/3}(\log T)^{7/3},$$
--   the expectation being over the algorithm's own randomness;
--   2. for every such $T$, sequence and realization of the randomness, the run performs at most $C\,T^c$ unit-cost operations.
--
--   The learner observes only the trade bit of each round. The comparator ranges over all of $[0,1]^2$, including $p>q$, and the valuations are arbitrary reals in $[0,1]^2$.
--
--   **Formalization Note** Logarithms are natural. The algorithm's randomness is one uniform draw $j^\star\in\{1,\dots,J\}$ per round, independent across rounds; the expectation is the average over the $J^T$ outcomes. The operation count is the counter of the run in the cost model of OneRound.
--
--   Differences from the source:
--   - generalization: "there exists a polynomial time algorithm $\mathcal A$" (with $K=\Theta((T/\log^7T)^{1/3})$) → the explicit Algorithm 1 + OneRound at $K(T)=\max(2,\lceil (T/\log^7T)^{1/3}\rceil)$; reason: the paper's algorithm with an explicit admissible resolution; it witnesses the existential statement
--   - encoding: $R_T\le O(T^{2/3}\log^{7/3}T)$ → $\exists C>0$ with the bound $C\,T^{2/3}(\log T)^{7/3}$ for every $T\ge2$; reason: at $T=1$ the right side is $0$ while every algorithm has positive regret on some one-round sequence; $O(\cdot)$ is asymptotic in $T$
--   - encoding: "polynomial time" → the run's unit-cost operation count is at most $C\,T^c$ for every input and every realization of the randomness; reason: the paper's own count (p.23) is of real-arithmetic operations; bit complexity is not claimed
--   - encoding: $\sup_{(p,q)\in[0,1]^2}$ of the expected regret; natural $\log$ → the bound for every comparator $(p,q)\in[0,1]^2$; `Real.log`; reason: a supremum is at most $B$ iff every term is; the paper's logarithms are natural (p.21)
--   - encoding: the expectation over the learner's randomness → the uniform average over draw sequences $\omega:\{0,\dots,T-1\}\to\{0,\dots,J-1\}$; reason: Algorithm 1's only randomness is the independent uniform $j^\star$ of each OneRound call
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Theorem 4.1, p.16 (PDF 18); proof §4.2.2, pp.22–23 (PDF 24–25)

import Mathlib
import Definitions.Def_BilateralProfit_Algorithm1

namespace BilateralProfit

/-- **Theorem 4.1 (Regret bound)**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256
e91e8127…), p.16 (PDF 18): there is a polynomial time algorithm whose regret against every
valuation sequence fixed in advance is `O(T^{2/3} log^{7/3} T)`.

Stated for the paper's algorithm (Algorithm 1 with OneRound, eqs. (5), (6), (8)) at the
resolution `K(T) = Kpin T`. Both clauses share the constant `C`:
1. for every horizon `T ≥ 2`, every valuation sequence `S ∈ ([0,1]²)^T` and every comparator
   `(p, q) ∈ [0,1]²`, `Σ_t E[Profit_t(p, q) − Profit_t(p_t, q_t)] ≤ C T^{2/3} (log T)^{7/3}`,
   the expectation being over the algorithm's own randomness;
2. for every such `T`, `S` and every realization `ω` of the randomness, the run performs at
   most `C T^c` unit-cost operations.

**Formalization Note.** `O(·)` is `∃ C > 0` for all `T ≥ 2` (at `T = 1` the right side is `0`).
The supremum over comparators is written as a bound for every comparator. `log` is the natural
logarithm. The cost model is the one of `OneRound` (unit-cost real arithmetic, `log`,
comparisons, table reads and writes, loop dispatch), counted by the program itself. -/
theorem theorem_4_1_regret_bound :
    ∃ C c : ℝ, 0 < C ∧ ∀ T : ℕ, 2 ≤ T →
      (∀ S : Fin T → ℝ × ℝ, (∀ t, S t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) →
        ∀ p q : ℝ, p ∈ Set.Icc (0 : ℝ) 1 → q ∈ Set.Icc (0 : ℝ) 1 →
          ∑ t, (profit (S t) (p, q) - expProfit (Kpin T) T S t) ≤
            C * (T : ℝ) ^ ((2 : ℝ) / 3) * Real.log T ^ ((7 : ℝ) / 3)) ∧
      (∀ S : Fin T → ℝ × ℝ, (∀ t, S t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) →
        ∀ ω : Fin T → Fin (Jpar (Kpin T)),
          (alg1Cost (Kpin T) T S ω : ℝ) ≤ C * (T : ℝ) ^ c) := by sorry

end BilateralProfit
