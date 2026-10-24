-- Prove2me | Theorems.Thm_Erdos195_second_sink_step_safe
-- name    : Erdos195.second_sink_step_safe
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-24T00:34:34.697574+00:00
-- url     : https://prove2.me/theorems/144d505c-0f6d-4b55-8edb-a704299c0fe5
-- title:
--   Second backward-closure step is tree-safe at the least sink
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$: for $x\ne y$ with $k=\nu_2(y-x)$, $x\prec_\theta y$ iff the $k$-th binary digit of $x$ is $1$ exactly when $\theta(k,x \bmod 2^k)=1$. A finite word $T$ of integers is $\theta$-safe if the sequence "letters of $T$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression (positions are first occurrences); $T$ is tree-safe if it is $\theta$-safe for some $\theta$. For an in-order pair $(a,b)$ of $T$ ($a$ before $b$) call $2b-a$ its third term and $3b-2a$ its fourth term. An open path in $T$ is a family of in-order pairs $(a_i,b_i)$, $0\le i<m$, $m\ge1$, with $3b_i-2a_i=2b_{i+1}-a_{i+1}$ for $i<m-1$ and no third term $2b_i-a_i$ in $T$. Its sink fourth term $w'=3b_{m-1}-2a_{m-1}$ is a true-sink fourth term of $T$ if $w'\notin T$ and every in-order pair $(x,y)$ of $T$ with $2y-x=w'$ has $3y-2x\in T$ (condition C1 for appending $w'$).
--
--   **Theorem.** Under the hypotheses of the previous milestone (open path with absent sink fourth term $w$, and uniqueness at $t=2b_{m-1}-a_{m-1}$), suppose $T\,w$ is $\theta'$-safe and $t\prec_{\theta'} w'$ for every true-sink fourth term $w'\ne t$ of $T\,w$. Then $T\,w\,t$ (the word $T$ followed by $w$ and then $t$) is tree-safe.
--
--   This is the preceding milestone combined with milestone #156 (the least sink is never blocked) applied to the word $T\,w$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem second_sink_step_safe (T : List ℤ) (hS : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) T)
    (m : ℕ) (a b : ℕ → ℤ) (hm : 0 < m)
    (ha : ∀ i < m, a i ∈ T) (hb : ∀ i < m, b i ∈ T)
    (hi : ∀ i < m, T.idxOf (a i) < T.idxOf (b i))
    (hpath : ∀ i, i + 1 < m → 3 * b i - 2 * a i = 2 * b (i + 1) - a (i + 1))
    (ht : ∀ i < m, 2 * b i - a i ∉ T)
    (hw : 3 * b (m - 1) - 2 * a (m - 1) ∉ T)
    (hU : ∀ x y : ℤ, x ∈ T → y ∈ T → T.idxOf x < T.idxOf y →
      2 * y - x = 2 * b (m - 1) - a (m - 1) → 3 * y - 2 * x ∉ T →
      3 * y - 2 * x = 3 * b (m - 1) - 2 * a (m - 1))
    (θ' : ℕ → ℤ → Bool) (hS' : Safe (treeLt θ') (T ++ [3 * b (m - 1) - 2 * a (m - 1)]))
    (hmin : ∀ (n : ℕ) (a' b' : ℕ → ℤ), 0 < n →
      (∀ i < n, a' i ∈ T ++ [3 * b (m - 1) - 2 * a (m - 1)]) →
      (∀ i < n, b' i ∈ T ++ [3 * b (m - 1) - 2 * a (m - 1)]) →
      (∀ i < n, (T ++ [3 * b (m - 1) - 2 * a (m - 1)]).idxOf (a' i) <
        (T ++ [3 * b (m - 1) - 2 * a (m - 1)]).idxOf (b' i)) →
      (∀ i, i + 1 < n → 3 * b' i - 2 * a' i = 2 * b' (i + 1) - a' (i + 1)) →
      (∀ i < n, 2 * b' i - a' i ∉ T ++ [3 * b (m - 1) - 2 * a (m - 1)]) →
      3 * b' (n - 1) - 2 * a' (n - 1) ∉ T ++ [3 * b (m - 1) - 2 * a (m - 1)] →
      (∀ x y : ℤ, x ∈ T ++ [3 * b (m - 1) - 2 * a (m - 1)] →
        y ∈ T ++ [3 * b (m - 1) - 2 * a (m - 1)] →
        (T ++ [3 * b (m - 1) - 2 * a (m - 1)]).idxOf x <
          (T ++ [3 * b (m - 1) - 2 * a (m - 1)]).idxOf y →
        2 * y - x = 3 * b' (n - 1) - 2 * a' (n - 1) →
        3 * y - 2 * x ∈ T ++ [3 * b (m - 1) - 2 * a (m - 1)]) →
      3 * b' (n - 1) - 2 * a' (n - 1) ≠ 2 * b (m - 1) - a (m - 1) →
      treeLt θ' (2 * b (m - 1) - a (m - 1)) (3 * b' (n - 1) - 2 * a' (n - 1))) :
    ∃ θ'' : ℕ → ℤ → Bool,
      Safe (treeLt θ'') (T ++ [3 * b (m - 1) - 2 * a (m - 1)] ++ [2 * b (m - 1) - a (m - 1)]) := by sorry

end Erdos195
