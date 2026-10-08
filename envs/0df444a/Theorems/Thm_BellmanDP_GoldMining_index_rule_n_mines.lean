-- Prove2me | Theorems.Thm_BellmanDP_GoldMining_index_rule_n_mines
-- name    : BellmanDP.GoldMining.index_rule_n_mines
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T15:14:41.387992+00:00
-- url     : https://prove2.me/theorems/dcdefce0-46d0-4ec0-a1d7-883ddbf620a5
-- title:
--   Chapter II, Theorem 4 — the index rule $D_i(x)=(\sum_k p_{ik}c_{ik})x_i/(1-\sum_k p_{ik})$ for $n$ mines
-- statement:
--   Consider $n \ge 1$ mines holding amounts $x = (x_1, \dots, x_n)$, $x_i \ge 0$, and $K$ possible outcomes for each use of the machine. Using mine $i$ produces outcome $k$ with probability $p_{ik}$, yields the gold $c_{ik}x_i$ and leaves $c'_{ik}x_i$ in mine $i$; with the remaining probability $1 - \sum_k p_{ik}$ the machine is destroyed. Assume
--   $$\text{(a)}\ \ p_{ik} \ge 0,\ \ \sum_{k=1}^{K} p_{ik} < 1 \ (i = 1,\dots,n);\qquad \text{(b)}\ \ 1 \ge c_{ik} \ge 0,\ \ c_{ik} + c'_{ik} = 1.$$
--   Then the functional equation
--   $$f(x_1,\dots,x_n) = \max_{i}\ \sum_{k=1}^{K} p_{ik}\bigl[c_{ik}x_i + f(x_1,\dots,c'_{ik}x_i,\dots,x_n)\bigr] \tag{4}$$
--   has a solution $f$ bounded on every box $0 \le x_i \le \bar X_i$, any two such solutions coincide on the orthant, and the solution obeys the index rule: with the decision functions
--   $$D_i(x) = \frac{\sum_{k=1}^{K} p_{ik}c_{ik}}{1-\sum_{k=1}^{K} p_{ik}}\,x_i,$$
--   at every state $x$ in the orthant, every index $i$ that maximizes $D_i(x)$ over $i = 1, \dots, n$ attains the maximum in (4). In case of equality among the $D_i$, it is a matter of indifference which maximizing index is used.
--
--   This is the most general index rule of the chapter; Theorem 2 ($n = 2$, one outcome) and Theorem 3 ($n = 2$) are special cases.
--
--   **Formalization Note** Mines are indexed by `Fin n` and outcomes by `Fin K`. The hypothesis $n \ge 1$ is added: with no mine the maximum in (4) is over an empty set. "The solution" is the unique solution in the class of functions bounded on every box (the $n$-mine form of Theorem 1's class, per the book's footnote 7), and its existence and uniqueness in that class are part of the statement. The conclusion is the book's: a maximizer of $D$ is an optimal choice; the statement does not assert that non-maximizers are suboptimal.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter II, § 10, Theorem 4, p. 70

import Mathlib
import Definitions.Def_BellmanDP_GoldMining_MultiOutcome

namespace BellmanDP.GoldMining

/-- Bellman, *Dynamic Programming*, Ch. II, Theorem 4, p. 70: `n ≥ 1` mines, `K` outcomes per use.
Under (5): `p_ik ≥ 0`, `Σ_k p_ik < 1` for each `i`, `0 ≤ c_ik ≤ 1`, `c_ik + c'_ik = 1`, the
equation (4) has a solution bounded on every box `0 ≤ x_i ≤ X̄_i`, unique there on the orthant,
and at every state `x ≥ 0` any index `i` maximizing the decision function
`D_i(x) = (Σ_k p_ik c_ik) x_i / (1 − Σ_k p_ik)` attains the maximum in (4) (in case of equality
among maximizers, any of them may be used). -/
theorem index_rule_n_mines (n K : ℕ) (hn : 0 < n) (p c c' : Fin n → Fin K → ℝ)
    (hp : ∀ i k, 0 ≤ p i k) (hps : ∀ i, ∑ k, p i k < 1)
    (hc0 : ∀ i k, 0 ≤ c i k) (hc1 : ∀ i k, c i k ≤ 1) (hc' : ∀ i k, c i k + c' i k = 1) :
    ∃ f : (Fin n → ℝ) → ℝ, IsNMineSolution p c c' f ∧ BoundedOnBoxes f ∧
      (∀ g : (Fin n → ℝ) → ℝ, IsNMineSolution p c c' g → BoundedOnBoxes g →
        ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → g x = f x) ∧
      ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → ∀ i : Fin n,
        (∀ j : Fin n, decisionFunction p c x j ≤ decisionFunction p c x i) →
          f x = mineOption p c c' f x i := by sorry

end BellmanDP.GoldMining
