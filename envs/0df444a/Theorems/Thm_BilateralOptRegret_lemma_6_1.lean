-- Prove2me | Theorems.Thm_BilateralOptRegret_lemma_6_1
-- name    : BilateralOptRegret.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:40.826172+00:00
-- url     : https://prove2.me/theorems/3e9421fc-0db7-485f-a123-d4b305954061
-- title:
--   Lemma 6.1 — fixed-endpoint learning by BinS
-- statement:
--   Let $a<b$ in $\{0,\dots,K-1\}$, let $W$ be a nonempty set of rows, $\beta\in(0,1]$, $\delta_0\in(0,1)$, and let $L$ be a law on $[0,1]^2$. With probability at least $1-\delta_0$, Algorithm 4 returns estimates with
--   $$|\hat P_{a,b}(w)-P_{a,b}(w)|\le\beta\quad\forall w\in W,$$
--   and on the same event the number of rows at which observations are collected is at most
--   $$2+\frac{2\lceil\log_2K\rceil\,\mathbb P\big(X\in(z_a,z_b]\times(z_{\min W},z_{\max W}]\big)}{\beta}.$$
--   Moreover, at each such row the algorithm collects $n_B=\lceil32\beta^{-2}\log(4K/\delta_0)\rceil$ observations at each of the two endpoints, and nothing else.
--
--   The cost thus scales with the probability mass of the rectangle, not with the number of rows.
--
--   Differences from the source:
--   - encoding: a queryable set $G_{qry}$ fixed in the statement → no such argument; $W$ is arbitrary, and all queries are at the two endpoints on rows of $W$; reason: the pseudocode reads only $W$, and the conclusions do not mention $G_{qry}$; eligibility is imposed where BinS is called
--   - generalization: "at each such row, the algorithm collects $n_B$ observations" → the clause holds on every run (`Sure`), and it also says queries stay on $W$ at the endpoints; reason: this holds for every observation sequence, so in particular on the event
--   - encoding: $\lceil\log_2K\rceil$ → `Nat.clog 2 K`; reason: the same integer
--   - encoding: $K\ge 2$ with $K-1$ a power of two (standing, p.13) → $K=2^n+1$, indices `Fin (2^n+1)`, $\ell_K=n+1$; reason: the page assumes this throughout §§4–8; every such $K$ has this form
--   - encoding: a procedure → a deterministic adaptive program `QTree` over grid actions, with the query list from `traced`; reason: Algorithms 1, 3, 4 use no internal randomness, and a program cannot read the law; the clauses on one event are an event on (output, query list)
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Lemma 6.1, p.22 (repeated pp.44–45; proof pp.45–46)

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Program
import Definitions.Def_BilateralOptRegret_BinS

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-- **Lemma 6.1**, Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.22 (repeated pp.44–45; proof pp.45–46): fixed-endpoint learning.

Fix `a < b`, a nonempty set of rows `W`, `β ∈ (0, 1]`, `δ₀ ∈ (0, 1)`. With probability at least `1 − δ₀`, Algorithm 4 returns `P̂` with
`|P̂_{a,b}(w) − P_{a,b}(w)| ≤ β` for all `w ∈ W`, and on the same event collects observations at no more than
`2 + 2⌈log₂ K⌉ P(X ∈ (z_a, z_b] × (z_{min W}, z_{max W}]) / β` rows, (11). On every run, all observations are at the two endpoints on rows of
`W`, and at each sampled row exactly `n_B = ⌈32 β⁻² log(4K/δ₀)⌉` observations are collected at each endpoint.

**Formalization Note.** `P_{a,b}(w)` is `rowDiff L K w b a`. `⌈log₂ K⌉` is `Nat.clog 2 K`. The queryable set of the printed statement does not
enter its conclusions: the pseudocode reads only `W`, which is why the program has no such argument; the eligibility of `W` is imposed where
BinS is called. The "moreover" clause is stated on every run (`Sure`), which is stronger than on the event. -/
theorem lemma_6_1 (n : ℕ) (a b : Idx n) (hab : a < b) (W : Finset (Idx n)) (hW : W.Nonempty)
    (β δ₀ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hδ : 0 < δ₀) (hδ1 : δ₀ < 1)
    (L : Measure (ℝ × ℝ)) (hL : IsValLaw L) :
    ENNReal.ofReal (1 - δ₀) ≤
      succProb L (Kof n) (binS a b β δ₀ W) (fun o =>
        (∀ w ∈ W, |o.1 w - rowDiff L (Kof n) w b a| ≤ β) ∧
        ((rowsOf o.2).card : ℝ) ≤
          2 + 2 * (Nat.clog 2 (Kof n) : ℝ) *
            (L (region (Kof n) a b (W.min' hW) (W.max' hW))).toReal / β) ∧
    Sure (fun o : (Idx n → ℝ) × List (Act n) =>
        (∀ q ∈ o.2, (q.1 = a ∨ q.1 = b) ∧ q.2 ∈ W) ∧
        ∀ w ∈ rowsOf o.2, o.2.count (a, w) = nBOf n β δ₀ ∧ o.2.count (b, w) = nBOf n β δ₀)
      (traced (binS a b β δ₀ W)) := by sorry

end BilateralOptRegret
