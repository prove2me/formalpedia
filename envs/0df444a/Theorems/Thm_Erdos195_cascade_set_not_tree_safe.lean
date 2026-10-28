-- Prove2me | Theorems.Thm_Erdos195_cascade_set_not_tree_safe
-- name    : Erdos195.cascade_set_not_tree_safe
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T05:34:48.449033+00:00
-- url     : https://prove2.me/theorems/e92a1959-3d54-457f-9b9c-7c157828f7a5
-- title:
--   Fixed-node fourth-term cascade: no tree-safe word on $(0,1,-1),2,3,w_0,\dots,w_m$
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. Let $w_j=2\cdot3^{j+1}-1$ (so $w_0=5$ and $w_{j+1}=3w_j+2$) and $m\ge0$. No word $Q$ beginning with $0,1,-1$, containing $w_m$, all of whose letters lie in
--   $$\{-1,0,1,2,3\}\cup\{w_0,w_1,\dots,w_m\},$$
--   is $\theta$-safe for any tree witness $\theta$. The pair $(1,-1)$ forces the value $1$ and the pair $(-1,w_m)$ forces the value $0$ at the same node $(1,1)$, and closing $(-1,w_m)$ by its fourth term creates $w_{m+1}$: an infinite fourth-term cascade at a fixed node, so no depth-type potential can make that repair rule terminate (Erdős Problem 195, tree-witness approach).
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. "Begins with" is the list prefix relation `<+:`; positions in a word are `List.idxOf`. The statement quantifies over every witness θ, so it holds in particular for all ε-orders.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statements from GPT 6 Astra (Oct 23 2026 'tree cascade' answers, generalized to all t / all m / all n), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem cascade_set_not_tree_safe (m : ℕ) (θ : ℕ → ℤ → Bool) (Q : List ℤ)
    (hpre : [0, 1, -1] <+: Q) (hw : 2 * (3 : ℤ) ^ (m + 1) - 1 ∈ Q)
    (hset : ∀ x ∈ Q, (x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∨
      ∃ j ≤ m, x = 2 * (3 : ℤ) ^ (j + 1) - 1) :
    ¬ Safe (treeLt θ) Q := by sorry

end Erdos195
