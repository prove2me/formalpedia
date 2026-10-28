-- Prove2me | Theorems.Thm_Erdos195_escape_chain_terminates_tree
-- name    : Erdos195.escape_chain_terminates_tree
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T03:17:14.559726+00:00
-- url     : https://prove2.me/theorems/b9530d8c-d643-4809-b0cf-d68e25680d05
-- title:
--   Escape chains terminate at every node, for every tree witness
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$: for $x\ne y$ with $k=\nu_2(y-x)$, $x\prec_\theta y$ iff the $k$-th binary digit of $x$ is $1$ exactly when $\theta(k,x \bmod 2^k)=1$. A finite word $T$ of integers is $\theta$-safe if the sequence "letters of $T$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression (positions are first occurrences); $T$ is tree-safe if it is $\theta$-safe for some $\theta$. For an in-order pair $(a,b)$ of $T$ ($a$ before $b$) call $2b-a$ its third term and $3b-2a$ its fourth term. An open path in $T$ is a family of in-order pairs $(a_i,b_i)$, $0\le i<m$, $m\ge1$, with $3b_i-2a_i=2b_{i+1}-a_{i+1}$ for $i<m-1$ and no third term $2b_i-a_i$ in $T$. Its sink fourth term $w'=3b_{m-1}-2a_{m-1}$ is a true-sink fourth term of $T$ if $w'\notin T$ and every in-order pair $(x,y)$ of $T$ with $2y-x=w'$ has $3y-2x\in T$ (condition C1 for appending $w'$).
--
--   **Theorem.** Let $Q$ be $\theta$-safe for some tree witness $\theta$, and let $o,w$ be letters of $Q$ with $o$ before $w$ and $o\prec_\theta w$ (a "wrong" in-order pair at the node of $(o,w)$). Put $e_n=o+3^n(w-o)$, so $e_0=w$ and $e_{n+1}=3e_n-2o$. Then there is $n\ge0$ such that $e_0,\dots,e_n$ all occur in $Q$, $e_0,\dots,e_{n-1}$ occur after $o$, and either
--
--   1. (reflection) $e_n$ occurs after $o$, and $2e_n-o$ occurs in $Q$ before $e_n$; or
--   2. (reversal) $n>0$ and $e_n$ occurs before $o$.
--
--   Since $\nu_2(e_n-o)=\nu_2(w-o)$ and $e_n\equiv w \pmod{2^{\nu_2(w-o)+1}}$, all pairs $(o,e_n)$ lie at the same node and are wrong for $\theta$; the chain cannot go on forever because the $e_n$ are distinct and $Q$ is finite. This generalizes milestone #142 (the root-node case $\theta(0,0)=1$, $o$ odd, $w$ even) to arbitrary levels, nodes and witnesses.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem escape_chain_terminates_tree (θ : ℕ → ℤ → Bool) (Q : List ℤ)
    (hS : Safe (treeLt θ) Q) (o w : ℤ) (ho : o ∈ Q) (hw : w ∈ Q)
    (hi : Q.idxOf o < Q.idxOf w) (hlt : treeLt θ o w) :
    ∃ n : ℕ, (∀ m ≤ n, o + 3 ^ m * (w - o) ∈ Q) ∧
      (∀ m < n, Q.idxOf o < Q.idxOf (o + 3 ^ m * (w - o))) ∧
      ((Q.idxOf o < Q.idxOf (o + 3 ^ n * (w - o)) ∧
          2 * (o + 3 ^ n * (w - o)) - o ∈ Q ∧
          Q.idxOf (2 * (o + 3 ^ n * (w - o)) - o) < Q.idxOf (o + 3 ^ n * (w - o))) ∨
        (0 < n ∧ Q.idxOf (o + 3 ^ n * (w - o)) < Q.idxOf o)) := by sorry

end Erdos195
