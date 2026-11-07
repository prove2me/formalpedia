-- Prove2me | Theorems.Thm_BilateralOptRegret_lemma_7_2
-- name    : BilateralOptRegret.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:40:17.717338+00:00
-- url     : https://prove2.me/theorems/d5394256-1af1-4e5b-b5ba-e09e7e82a1c9
-- title:
--   Lemma 7.2 — canonical dyadic junctions
-- statement:
--   Let $a<b$ in $\{0,\dots,K-1\}$. The decomposition $\mathcal B(b,a)$ contains at most $2\log_2K$ intervals. Moreover, every junction $k$ between two consecutive intervals is an internal index, and its permitted interval $I_k$ contains at least one of $a$ and $b$.
--
--   This purely combinatorial fact is what makes a target endpoint available as a replacement for each junction.
--
--   Differences from the source:
--   - generalization: "every internal junction $k$" → every junction, with the added assertion that it is internal; reason: a junction lies strictly between $a$ and $b$, so it is internal; the printed claim is the second part of the Lean conjunct
--   - encoding: a set $\mathcal B(b,a)$ → the greedy list of App. B; the claim concerns its consecutive elements; reason: the page speaks of "consecutive intervals" of this chain
--   - encoding: $K\ge 2$ with $K-1$ a power of two (standing, p.13) → $K=2^n+1$, indices `Fin (2^n+1)`, $\ell_K=n+1$; reason: the page assumes this throughout §§4–8; every such $K$ has this form
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Lemma 7.2, p.29

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Dyadic

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-- **Lemma 7.2**, Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.29: canonical dyadic junctions.

For `a < b`, `B(b, a)` has at most `2 log₂ K` intervals, and for every junction `k` between two consecutive intervals, `I_k` contains `a` or `b`.

**Formalization Note.** `B` is the greedy list of App. B; the claim fails for a non-maximal chain. Lean also asserts that each junction is internal, so `I_k` is
never read at a boundary index. At `n = 0` the chain is empty and the statement holds trivially. -/
theorem lemma_7_2 (n : ℕ) (a b : Idx n) (hab : a < b) :
    ((B n b a).length : ℝ) ≤ 2 * Real.logb 2 (Kof n : ℝ) ∧
    ∀ k ∈ junctions (B n b a), k ∈ internal n ∧ (a ∈ perm k ∨ b ∈ perm k) := by sorry

end BilateralOptRegret
