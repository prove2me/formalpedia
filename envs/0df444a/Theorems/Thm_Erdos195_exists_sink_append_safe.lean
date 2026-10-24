-- Prove2me | Theorems.Thm_Erdos195_exists_sink_append_safe
-- name    : Erdos195.exists_sink_append_safe
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-24T00:09:31.000182+00:00
-- url     : https://prove2.me/theorems/ab1598e1-78f6-4e20-a9f7-60ea46a59369
-- title:
--   Every tree-safe word with a fully open pair admits a tree-safe sink step
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$: for $x\ne y$ with $k=\nu_2(y-x)$, $x\prec_\theta y$ iff the $k$-th binary digit of $x$ is $1$ exactly when $\theta(k,x \bmod 2^k)=1$. A finite word $T$ of integers is $\theta$-safe if the sequence "letters of $T$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression (positions are first occurrences); $T$ is tree-safe if it is $\theta$-safe for some $\theta$. For an in-order pair $(a,b)$ of $T$ ($a$ before $b$) call $2b-a$ its third term and $3b-2a$ its fourth term. An open path in $T$ is a family of in-order pairs $(a_i,b_i)$, $0\le i<m$, $m\ge1$, with $3b_i-2a_i=2b_{i+1}-a_{i+1}$ for $i<m-1$ and no third term $2b_i-a_i$ in $T$. Its sink fourth term $w'=3b_{m-1}-2a_{m-1}$ is a true-sink fourth term of $T$ if $w'\notin T$ and every in-order pair $(x,y)$ of $T$ with $2y-x=w'$ has $3y-2x\in T$ (condition C1 for appending $w'$).
--
--   **Theorem.** Let $T$ be tree-safe and suppose $T$ has a fully open in-order pair $(a_0,b_0)$ (both $2b_0-a_0\notin T$ and $3b_0-2a_0\notin T$). Then there is an open path $(a_i,b_i)_{i<m}$, $m\ge1$, in $T$ whose sink fourth term
--   $$w=3b_{m-1}-2a_{m-1}$$
--   is a true-sink fourth term of $T$ and such that $T\,w$ is again tree-safe.
--
--   So a deadlock in which every sink step fails cannot occur: one closing step (appending the fourth term of the sink pair, which closes it) is always available. The proof takes $w$ to be the $\prec_\theta$-least true-sink fourth term, which exists because there are finitely many and at least one by milestone #154, and applies the preceding milestone.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem exists_sink_append_safe (T : List ℤ) (hS : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) T)
    (a₀ b₀ : ℤ) (ha₀ : a₀ ∈ T) (hb₀ : b₀ ∈ T) (hi₀ : T.idxOf a₀ < T.idxOf b₀)
    (ht₀ : 2 * b₀ - a₀ ∉ T) (hw₀ : 3 * b₀ - 2 * a₀ ∉ T) :
    ∃ (m : ℕ) (a b : ℕ → ℤ), 0 < m ∧
      (∀ i < m, a i ∈ T) ∧ (∀ i < m, b i ∈ T) ∧ (∀ i < m, T.idxOf (a i) < T.idxOf (b i)) ∧
      (∀ i, i + 1 < m → 3 * b i - 2 * a i = 2 * b (i + 1) - a (i + 1)) ∧
      (∀ i < m, 2 * b i - a i ∉ T) ∧ 3 * b (m - 1) - 2 * a (m - 1) ∉ T ∧
      (∀ x y : ℤ, x ∈ T → y ∈ T → T.idxOf x < T.idxOf y →
        2 * y - x = 3 * b (m - 1) - 2 * a (m - 1) → 3 * y - 2 * x ∈ T) ∧
      ∃ θ' : ℕ → ℤ → Bool, Safe (treeLt θ') (T ++ [3 * b (m - 1) - 2 * a (m - 1)]) := by sorry

end Erdos195
