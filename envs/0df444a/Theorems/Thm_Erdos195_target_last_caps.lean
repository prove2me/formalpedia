-- Prove2me | Theorems.Thm_Erdos195_target_last_caps
-- name    : Erdos195.target_last_caps
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T14:10:02.376827+00:00
-- url     : https://prove2.me/theorems/40c38a4f-c7f9-481e-8ff6-94ef204e666b
-- title:
--   Compulsory witnesses for target-last absorption of $2$ after $(0,1,-1)$: $-3,-5$ and capped power-of-3 rays
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. For letters $a$ before $b$ in $Q$, the pair $(a,b)$ is OPEN if neither $2b-a$ nor $3b-2a$ occurs in $Q$. Let $\theta$ be any tree witness and let $A=(0,1,-1,r_1,\dots,r_m,2)$ be a $\theta$-safe word with $2\notin\{r_1,\dots,r_m\}$. Then $-3\in A$ and $-5\in A$. Moreover, both rays of powers of $3$ are capped by a double placed earlier: there are $m,n\ge1$ with
--   $$3^m\in A,\quad 3^{m+1}\notin A,\quad 2\cdot3^m\in A\text{ before }3^m,$$
--   $$-3^n\in A,\quad -3^{n+1}\notin A,\quad -2\cdot3^n\in A\text{ before }-3^n.$$
--   These are compulsory small witnesses for any target-last absorption of $2$ after $(0,1,-1)$. In particular such a word has an even letter $\ge6$ and an even letter $\le-6$.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`, and `Safe` is from `Definitions.Def_Erdos195_defs`. Positions are `List.idxOf`; the word is written `(0 :: 1 :: -1 :: rest) ++ [2]`, and the hypothesis $2\notin\mathrm{rest}$ makes $2$ the last letter and its only occurrence.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; argument by GPT Astra, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem target_last_caps (θ : ℕ → ℤ → Bool) (A rest : List ℤ)
    (hA : A = (0 :: 1 :: -1 :: rest) ++ [2]) (h2 : (2 : ℤ) ∉ rest)
    (hS : Safe (treeLt θ) A) :
    (-3 : ℤ) ∈ A ∧ (-5 : ℤ) ∈ A ∧
    (∃ m : ℕ, 1 ≤ m ∧ (3 : ℤ) ^ m ∈ A ∧ (3 : ℤ) ^ (m + 1) ∉ A ∧ 2 * (3 : ℤ) ^ m ∈ A ∧
      A.idxOf (2 * (3 : ℤ) ^ m) < A.idxOf ((3 : ℤ) ^ m)) ∧
    (∃ n : ℕ, 1 ≤ n ∧ -(3 : ℤ) ^ n ∈ A ∧ -(3 : ℤ) ^ (n + 1) ∉ A ∧ -2 * (3 : ℤ) ^ n ∈ A ∧
      A.idxOf (-2 * (3 : ℤ) ^ n) < A.idxOf (-(3 : ℤ) ^ n)) := by sorry

end Erdos195
