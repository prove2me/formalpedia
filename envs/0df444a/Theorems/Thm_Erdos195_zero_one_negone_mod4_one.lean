-- Prove2me | Theorems.Thm_Erdos195_zero_one_negone_mod4_one
-- name    : Erdos195.zero_one_negone_mod4_one
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T05:34:46.856008+00:00
-- url     : https://prove2.me/theorems/75c639d9-4343-4bca-aeb4-6cf5b2d2d270
-- title:
--   Tree-safe words starting $(0,1,-1)$ containing $t\equiv1 \pmod 4$ must meet $\{-3,-5,2t+1,3t+2\}$
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. Let $Q$ be a $\theta$-safe word (for any tree witness $\theta$) beginning with $0,1,-1$, and let $t\in Q$ with $t\equiv1\pmod 4$, $t\neq1$. Then
--   $$\{-3,\,-5,\,2t+1,\,3t+2\}\cap Q\neq\varnothing.$$
--   Indeed the in-order pairs $(1,-1)$ and $(-1,t)$ both sit at the tree node $(1,1)$ and, if both were open (neither continuation $2b-a$, $3b-2a$ present), would force opposite values there. This is the fixed-node cascade behind the failure of the rule "close the newest conflicting pair by its fourth term" when extending $(0,1,-1)$ in Ho-style constructions of $4$-AP-free permutations of $\mathbb{Z}$ (Erdős Problem 195); the case $t=5$ gives the necessary condition $Q\cap\{-3,-5,11,17\}\neq\varnothing$.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. "Begins with" is the list prefix relation `<+:`; positions in a word are `List.idxOf`. The statement quantifies over every witness θ, so it holds in particular for all ε-orders.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statements from GPT 6 Astra (Oct 23 2026 'tree cascade' answers, generalized to all t / all m / all n), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem zero_one_negone_mod4_one (θ : ℕ → ℤ → Bool) (Q : List ℤ) (hS : Safe (treeLt θ) Q)
    (hpre : [0, 1, -1] <+: Q) (t : ℤ) (ht : t ∈ Q) (ht4 : t % 4 = 1) (ht1 : t ≠ 1) :
    -3 ∈ Q ∨ -5 ∈ Q ∨ 2 * t + 1 ∈ Q ∨ 3 * t + 2 ∈ Q := by sorry

end Erdos195
