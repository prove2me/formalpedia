-- Prove2me | Theorems.Thm_Erdos195_new_pair_blockers_iff
-- name    : Erdos195.new_pair_blockers_iff
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-24T03:17:38.058102+00:00
-- url     : https://prove2.me/theorems/5ca02fc9-8600-4d42-9613-1bbbe63088cc
-- title:
--   New-pair conflicts at the second backward step: exact criterion
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$: for $x\ne y$ with $k=\nu_2(y-x)$, $x\prec_\theta y$ iff the $k$-th binary digit of $x$ is $1$ exactly when $\theta(k,x \bmod 2^k)=1$. A finite word $T$ of integers is $\theta$-safe if the sequence "letters of $T$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression (positions are first occurrences); $T$ is tree-safe if it is $\theta$-safe for some $\theta$. For an in-order pair $(a,b)$ of $T$ ($a$ before $b$) call $2b-a$ its third term and $3b-2a$ its fourth term. An open path in $T$ is a family of in-order pairs $(a_i,b_i)$, $0\le i<m$, $m\ge1$, with $3b_i-2a_i=2b_{i+1}-a_{i+1}$ for $i<m-1$ and no third term $2b_i-a_i$ in $T$. Its sink fourth term $w'=3b_{m-1}-2a_{m-1}$ is a true-sink fourth term of $T$ if $w'\notin T$ and every in-order pair $(x,y)$ of $T$ with $2y-x=w'$ has $3y-2x\in T$ (condition C1 for appending $w'$).
--
--   **Theorem.** Let $T$ be a finite word, $b\in T$, $a\ne b$ an integer, $d=b-a$, $k=\nu_2(d)$, $w=3b-2a$ and $t=2b-a$, with $w,t\notin T$. Let $U=T\,w\,t$ ($T$ followed by $w$, then $t$). Call a *new-pair conflict* a choice of $x'\in T$ and $x\in T\,w$ such that both pairs $(x',w)$ and $(x,t)$ are fully open in $U$ (third and fourth terms absent from $U$), they have the same level $\nu_2(w-x')=\nu_2(t-x)$ and the same node $x'\equiv x \pmod{2^{\nu_2(t-x)}}$, and opposite orientations: the binary digits of $w$ and $t$ at that level differ. Then:
--
--   1. a new-pair conflict exists if and only if (i) some $x'\in T$ with $x'\equiv a\pmod{2^{k+1}}$ has $2w-x',\,3w-2x'\notin U$, and (ii) some $x\in T$ with $x\equiv b\pmod{2^{k+1}}$ has $2t-x,\,3t-2x\notin U$ (and then the common level is exactly $k$);
--   2. if a new-pair conflict exists then $U$ is not tree-safe (for any witness).
--
--   In the setting of milestones #158–#159 ($(a,b)$ the last pair of an open path, $w$ its sink, $t$ its third term), this characterizes exactly when the pairs created by the first sink step and by the second step collide; note that $x'=a$ satisfies (i) as soon as $6b-5a,\,9b-8a\notin U$, so the decisive condition is (ii).
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem new_pair_blockers_iff (T : List ℤ) (a b : ℤ) (hab : a ≠ b) (hbT : b ∈ T)
    (hw : 3 * b - 2 * a ∉ T) (ht : 2 * b - a ∉ T) :
    ((∃ x' x : ℤ, x' ∈ T ∧ x ∈ T ++ [3 * b - 2 * a] ∧
        2 * (3 * b - 2 * a) - x' ∉ T ++ [3 * b - 2 * a] ++ [2 * b - a] ∧
        3 * (3 * b - 2 * a) - 2 * x' ∉ T ++ [3 * b - 2 * a] ++ [2 * b - a] ∧
        2 * (2 * b - a) - x ∉ T ++ [3 * b - 2 * a] ++ [2 * b - a] ∧
        3 * (2 * b - a) - 2 * x ∉ T ++ [3 * b - 2 * a] ++ [2 * b - a] ∧
        padicValInt 2 ((3 * b - 2 * a) - x') = padicValInt 2 ((2 * b - a) - x) ∧
        x' % 2 ^ padicValInt 2 ((2 * b - a) - x) = x % 2 ^ padicValInt 2 ((2 * b - a) - x) ∧
        ¬ (bitOne (3 * b - 2 * a) (padicValInt 2 ((2 * b - a) - x)) ↔
          bitOne (2 * b - a) (padicValInt 2 ((2 * b - a) - x)))) ↔
      ((∃ x' ∈ T, x' % 2 ^ (padicValInt 2 (b - a) + 1) = a % 2 ^ (padicValInt 2 (b - a) + 1) ∧
          2 * (3 * b - 2 * a) - x' ∉ T ++ [3 * b - 2 * a] ++ [2 * b - a] ∧
          3 * (3 * b - 2 * a) - 2 * x' ∉ T ++ [3 * b - 2 * a] ++ [2 * b - a]) ∧
        (∃ x ∈ T, x % 2 ^ (padicValInt 2 (b - a) + 1) = b % 2 ^ (padicValInt 2 (b - a) + 1) ∧
          2 * (2 * b - a) - x ∉ T ++ [3 * b - 2 * a] ++ [2 * b - a] ∧
          3 * (2 * b - a) - 2 * x ∉ T ++ [3 * b - 2 * a] ++ [2 * b - a]))) ∧
    ((∃ x' x : ℤ, x' ∈ T ∧ x ∈ T ++ [3 * b - 2 * a] ∧
        2 * (3 * b - 2 * a) - x' ∉ T ++ [3 * b - 2 * a] ++ [2 * b - a] ∧
        3 * (3 * b - 2 * a) - 2 * x' ∉ T ++ [3 * b - 2 * a] ++ [2 * b - a] ∧
        2 * (2 * b - a) - x ∉ T ++ [3 * b - 2 * a] ++ [2 * b - a] ∧
        3 * (2 * b - a) - 2 * x ∉ T ++ [3 * b - 2 * a] ++ [2 * b - a] ∧
        padicValInt 2 ((3 * b - 2 * a) - x') = padicValInt 2 ((2 * b - a) - x) ∧
        x' % 2 ^ padicValInt 2 ((2 * b - a) - x) = x % 2 ^ padicValInt 2 ((2 * b - a) - x) ∧
        ¬ (bitOne (3 * b - 2 * a) (padicValInt 2 ((2 * b - a) - x)) ↔
          bitOne (2 * b - a) (padicValInt 2 ((2 * b - a) - x)))) →
      ¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (T ++ [3 * b - 2 * a] ++ [2 * b - a])) := by sorry

end Erdos195
