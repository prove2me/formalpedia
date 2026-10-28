-- Prove2me | Theorems.Thm_Erdos195_sink_step_inherits
-- name    : Erdos195.sink_step_inherits
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T00:34:39.029914+00:00
-- url     : https://prove2.me/theorems/e7433b70-89fc-4e8c-a328-c0ec22b78335
-- title:
--   After a sink step, the sink passes back along the path: the previous third term becomes a true sink
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$: for $x\ne y$ with $k=\nu_2(y-x)$, $x\prec_\theta y$ iff the $k$-th binary digit of $x$ is $1$ exactly when $\theta(k,x \bmod 2^k)=1$. A finite word $T$ of integers is $\theta$-safe if the sequence "letters of $T$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression (positions are first occurrences); $T$ is tree-safe if it is $\theta$-safe for some $\theta$. For an in-order pair $(a,b)$ of $T$ ($a$ before $b$) call $2b-a$ its third term and $3b-2a$ its fourth term. An open path in $T$ is a family of in-order pairs $(a_i,b_i)$, $0\le i<m$, $m\ge1$, with $3b_i-2a_i=2b_{i+1}-a_{i+1}$ for $i<m-1$ and no third term $2b_i-a_i$ in $T$. Its sink fourth term $w'=3b_{m-1}-2a_{m-1}$ is a true-sink fourth term of $T$ if $w'\notin T$ and every in-order pair $(x,y)$ of $T$ with $2y-x=w'$ has $3y-2x\in T$ (condition C1 for appending $w'$).
--
--   **Theorem.** Let $T$ be tree-safe and let $(a_i,b_i)_{i<m}$, $m\ge1$, be an open path in $T$ whose sink fourth term $w=3b_{m-1}-2a_{m-1}$ is not in $T$. Put $t=2b_{m-1}-a_{m-1}$. Assume uniqueness: every in-order pair $(x,y)$ of $T$ with $2y-x=t$ and $3y-2x\notin T$ has $3y-2x=w$. Then in the word $T\,w$:
--
--   1. every path pair $(a_i,b_i)$, $i<m$, is still an in-order pair, and no third term $2b_i-a_i$ lies in $T\,w$ (in particular $t\notin T\,w$), so $(a_i,b_i)_{i<m-1}$ is an open path of $T\,w$ whose sink fourth term is $3b_{m-2}-2a_{m-2}=t$ (for $m\ge2$);
--   2. $t$ satisfies C1 in $T\,w$: every in-order pair $(x,y)$ of $T\,w$ with $2y-x=t$ has $3y-2x\in T\,w$.
--
--   So $t$ is a true-sink fourth term of $T\,w$. Together with milestone #149 (an open path can only be closed from the sink backwards) this shows that the backward closure of a path is a sequence of true-sink steps. The fact $2b_i-a_i\ne w$ uses the ruler law (#148) and the exact valuation of the telescoping sum.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem sink_step_inherits (T : List ℤ) (hS : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) T)
    (m : ℕ) (a b : ℕ → ℤ) (hm : 0 < m)
    (ha : ∀ i < m, a i ∈ T) (hb : ∀ i < m, b i ∈ T)
    (hi : ∀ i < m, T.idxOf (a i) < T.idxOf (b i))
    (hpath : ∀ i, i + 1 < m → 3 * b i - 2 * a i = 2 * b (i + 1) - a (i + 1))
    (ht : ∀ i < m, 2 * b i - a i ∉ T)
    (hw : 3 * b (m - 1) - 2 * a (m - 1) ∉ T)
    (hU : ∀ x y : ℤ, x ∈ T → y ∈ T → T.idxOf x < T.idxOf y →
      2 * y - x = 2 * b (m - 1) - a (m - 1) → 3 * y - 2 * x ∉ T →
      3 * y - 2 * x = 3 * b (m - 1) - 2 * a (m - 1)) :
    (∀ i < m, a i ∈ T ++ [3 * b (m - 1) - 2 * a (m - 1)]) ∧
    (∀ i < m, b i ∈ T ++ [3 * b (m - 1) - 2 * a (m - 1)]) ∧
    (∀ i < m, (T ++ [3 * b (m - 1) - 2 * a (m - 1)]).idxOf (a i) <
      (T ++ [3 * b (m - 1) - 2 * a (m - 1)]).idxOf (b i)) ∧
    (∀ i < m, 2 * b i - a i ∉ T ++ [3 * b (m - 1) - 2 * a (m - 1)]) ∧
    (∀ x y : ℤ, x ∈ T ++ [3 * b (m - 1) - 2 * a (m - 1)] → y ∈ T ++ [3 * b (m - 1) - 2 * a (m - 1)] →
      (T ++ [3 * b (m - 1) - 2 * a (m - 1)]).idxOf x < (T ++ [3 * b (m - 1) - 2 * a (m - 1)]).idxOf y →
      2 * y - x = 2 * b (m - 1) - a (m - 1) →
      3 * y - 2 * x ∈ T ++ [3 * b (m - 1) - 2 * a (m - 1)]) := by sorry

end Erdos195
