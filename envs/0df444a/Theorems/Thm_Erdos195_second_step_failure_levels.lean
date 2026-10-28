-- Prove2me | Theorems.Thm_Erdos195_second_step_failure_levels
-- name    : Erdos195.second_step_failure_levels
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T03:41:27.308981+00:00
-- url     : https://prove2.me/theorems/9a903e9b-99d9-4d80-bbbc-c2d421bde8e0
-- title:
--   Failure of the second backward step is located by level
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$: for $x\ne y$ with $k=\nu_2(y-x)$, $x\prec_\theta y$ iff the $k$-th binary digit of $x$ is $1$ exactly when $\theta(k,x \bmod 2^k)=1$. A finite word $T$ of integers is $\theta$-safe if the sequence "letters of $T$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression (positions are first occurrences); $T$ is tree-safe if it is $\theta$-safe for some $\theta$. For an in-order pair $(a,b)$ of $T$ ($a$ before $b$) call $2b-a$ its third term and $3b-2a$ its fourth term. An open path in $T$ is a family of in-order pairs $(a_i,b_i)$, $0\le i<m$, $m\ge1$, with $3b_i-2a_i=2b_{i+1}-a_{i+1}$ for $i<m-1$ and no third term $2b_i-a_i$ in $T$. Its sink fourth term $w'=3b_{m-1}-2a_{m-1}$ is a true-sink fourth term of $T$ if $w'\notin T$ and every in-order pair $(x,y)$ of $T$ with $2y-x=w'$ has $3y-2x\in T$ (condition C1 for appending $w'$).
--
--   **Theorem.** Let $T$ be a finite word, $b\in T$, $a\ne b$, $k=\nu_2(b-a)$, $w=3b-2a\notin T$, $t=2b-a\notin T$, and let $Q=T\,w$ be $\theta$-safe. Assume $t$ passes C1 in $Q$ (every in-order pair $(x,y)$ of $Q$ with $2y-x=t$ has $3y-2x\in Q$). If $Q\,t$ is not tree-safe for any witness, then there exist $x\in T$ with $(x,t)$ fully open in $Q\,t$ ($2t-x,\,3t-2x\notin Q$) and a fully open in-order pair $(a',b')$ of $Q$ (third and fourth terms not in $Q$, neither equal to $t$) at the same level $j=\nu_2(b'-a')=\nu_2(t-x)$ and node $a'\equiv x\pmod{2^j}$ with opposite digits of $b'$ and $t$ at level $j$; moreover exactly one of:
--
--   1. (high) $j>k$ and $x\equiv a\pmod{2^{k+1}}$;
--   2. (level $k$) $j=k$, $x\equiv b\pmod{2^{k+1}}$, and the $k$-th digits of $b'$ and $b$ agree (the blocker has the orientation of $(a,b)$);
--   3. (low) $j<k$ and $w$ is already released at $x$ in $T$: $2w-x\in T$ or $3w-2x\in T$.
--
--   The low case uses that $b,t,w$ agree modulo $2^k$, so below level $k$ the pair $(x,w)$ of $Q$ would sit at the same node with the orientation of $(x,t)$ and conflict with $(a',b')$ unless released. This covers blockers among old pairs of $T$ as well as new pairs $(x',w)$, extending milestone #161 (new pairs only, level $k$) towards a full criterion for the second step of #158–#159.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem second_step_failure_levels (θ : ℕ → ℤ → Bool) (T : List ℤ) (a b : ℤ) (hab : a ≠ b)
    (hb : b ∈ T) (hwT : 3 * b - 2 * a ∉ T) (htT : 2 * b - a ∉ T)
    (hS : Safe (treeLt θ) (T ++ [3 * b - 2 * a]))
    (hC1 : ∀ x y : ℤ, x ∈ T ++ [3 * b - 2 * a] → y ∈ T ++ [3 * b - 2 * a] →
      (T ++ [3 * b - 2 * a]).idxOf x < (T ++ [3 * b - 2 * a]).idxOf y →
      2 * b - a = 2 * y - x → 3 * y - 2 * x ∈ T ++ [3 * b - 2 * a])
    (hbad : ¬ ∃ θ' : ℕ → ℤ → Bool, Safe (treeLt θ') (T ++ [3 * b - 2 * a] ++ [2 * b - a])) :
    ∃ x a' b' : ℤ, x ∈ T ∧ 2 * (2 * b - a) - x ∉ T ++ [3 * b - 2 * a] ∧
      3 * (2 * b - a) - 2 * x ∉ T ++ [3 * b - 2 * a] ∧
      a' ∈ T ++ [3 * b - 2 * a] ∧ b' ∈ T ++ [3 * b - 2 * a] ∧
      (T ++ [3 * b - 2 * a]).idxOf a' < (T ++ [3 * b - 2 * a]).idxOf b' ∧
      2 * b' - a' ∉ T ++ [3 * b - 2 * a] ∧ 3 * b' - 2 * a' ∉ T ++ [3 * b - 2 * a] ∧
      2 * b - a ≠ 2 * b' - a' ∧ 2 * b - a ≠ 3 * b' - 2 * a' ∧
      padicValInt 2 (b' - a') = padicValInt 2 ((2 * b - a) - x) ∧
      a' % 2 ^ padicValInt 2 (b' - a') = x % 2 ^ padicValInt 2 (b' - a') ∧
      ¬ (bitOne b' (padicValInt 2 (b' - a')) ↔ bitOne (2 * b - a) (padicValInt 2 (b' - a'))) ∧
      ((padicValInt 2 (b - a) < padicValInt 2 (b' - a') ∧
          x % 2 ^ (padicValInt 2 (b - a) + 1) = a % 2 ^ (padicValInt 2 (b - a) + 1)) ∨
        (padicValInt 2 (b' - a') = padicValInt 2 (b - a) ∧
          x % 2 ^ (padicValInt 2 (b - a) + 1) = b % 2 ^ (padicValInt 2 (b - a) + 1) ∧
          (bitOne b' (padicValInt 2 (b - a)) ↔ bitOne b (padicValInt 2 (b - a)))) ∨
        (padicValInt 2 (b' - a') < padicValInt 2 (b - a) ∧
          (2 * (3 * b - 2 * a) - x ∈ T ∨ 3 * (3 * b - 2 * a) - 2 * x ∈ T))) := by sorry

end Erdos195
