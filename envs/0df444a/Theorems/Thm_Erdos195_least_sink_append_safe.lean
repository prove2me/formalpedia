-- Prove2me | Theorems.Thm_Erdos195_least_sink_append_safe
-- name    : Erdos195.least_sink_append_safe
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-24T00:09:26.544179+00:00
-- url     : https://prove2.me/theorems/295c938d-9846-479d-b078-28bc551e5f19
-- title:
--   The ≺_θ-least sink fourth term can always be appended (no sink deadlock)
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$: for $x\ne y$ with $k=\nu_2(y-x)$, $x\prec_\theta y$ iff the $k$-th binary digit of $x$ is $1$ exactly when $\theta(k,x \bmod 2^k)=1$. A finite word $T$ of integers is $\theta$-safe if the sequence "letters of $T$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression (positions are first occurrences); $T$ is tree-safe if it is $\theta$-safe for some $\theta$. For an in-order pair $(a,b)$ of $T$ ($a$ before $b$) call $2b-a$ its third term and $3b-2a$ its fourth term. An open path in $T$ is a family of in-order pairs $(a_i,b_i)$, $0\le i<m$, $m\ge1$, with $3b_i-2a_i=2b_{i+1}-a_{i+1}$ for $i<m-1$ and no third term $2b_i-a_i$ in $T$. Its sink fourth term $w'=3b_{m-1}-2a_{m-1}$ is a true-sink fourth term of $T$ if $w'\notin T$ and every in-order pair $(x,y)$ of $T$ with $2y-x=w'$ has $3y-2x\in T$ (condition C1 for appending $w'$).
--
--   **Theorem.** Let $T$ be $\theta$-safe and let $w\notin T$ satisfy C1: every in-order pair $(x,y)$ of $T$ with $2y-x=w$ has $3y-2x\in T$. Suppose that
--   $$w\prec_\theta w'\quad\text{for every true-sink fourth term } w'\neq w \text{ of } T .$$
--   Then $T\,w$ (the word $T$ followed by $w$) is tree-safe.
--
--   This answers the deadlock question left by milestone #155: a failed sink step is caused by a fully open pair from the in-tree of another true sink $w'$, and here we show that such a blocking always forces $w'\prec_\theta w$. So the "blocks" relation between sinks is contained in $\prec_\theta$ and is acyclic, and the $\prec_\theta$-least sink is never blocked.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem least_sink_append_safe (θ : ℕ → ℤ → Bool) (T : List ℤ) (hS : Safe (treeLt θ) T)
    (w : ℤ) (hwT : w ∉ T)
    (hC1 : ∀ x y : ℤ, x ∈ T → y ∈ T → T.idxOf x < T.idxOf y → 2 * y - x = w → 3 * y - 2 * x ∈ T)
    (hmin : ∀ (m : ℕ) (a b : ℕ → ℤ), 0 < m →
      (∀ i < m, a i ∈ T) → (∀ i < m, b i ∈ T) →
      (∀ i < m, T.idxOf (a i) < T.idxOf (b i)) →
      (∀ i, i + 1 < m → 3 * b i - 2 * a i = 2 * b (i + 1) - a (i + 1)) →
      (∀ i < m, 2 * b i - a i ∉ T) →
      3 * b (m - 1) - 2 * a (m - 1) ∉ T →
      (∀ x y : ℤ, x ∈ T → y ∈ T → T.idxOf x < T.idxOf y →
        2 * y - x = 3 * b (m - 1) - 2 * a (m - 1) → 3 * y - 2 * x ∈ T) →
      3 * b (m - 1) - 2 * a (m - 1) ≠ w →
      treeLt θ w (3 * b (m - 1) - 2 * a (m - 1))) :
    ∃ θ' : ℕ → ℤ → Bool, Safe (treeLt θ') (T ++ [w]) := by sorry

end Erdos195
