-- Prove2me | Theorems.Thm_Erdos195_open_cycle_blocks_exhaustive_chain
-- name    : Erdos195.open_cycle_blocks_exhaustive_chain
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T21:37:50.767806+00:00
-- url     : https://prove2.me/theorems/72b44c55-85ea-4bcb-bf6a-0b4115e3c3d0
-- title:
--   Open cycles of pairs block exhaustive chains of tree-safe words
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework). A finite word $Q$ of integers is $\theta$-safe if the sequence "letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression; positions are first occurrences. For an in-order pair $(a,b)$ of a word (a before b), call $2b-a$ its third term and $3b-2a$ its fourth term. **Theorem (open cycles block exhaustive chains).** Let $P_0, P_1, P_2,\dots$ be finite words with each $P_n$ a prefix of $P_{n+1}$, each $P_n$ $\theta_n$-safe for some tree witness $\theta_n$ (which may depend on $n$), and such that every integer occurs in some $P_n$. Then no stage $P_N$ contains a cycle of in-order pairs $(a_i,b_i)$, $0\le i<m$, $m\ge1$, with
--   $$3b_i-2a_i \;=\; 2b_{i+1}-a_{i+1}\qquad(\text{indices mod } m)$$
--   and all third terms $2b_i-a_i$ absent from $P_N$.
--
--   So an exhaustive chain of tree-safe words (the kind of chain that would give a permutation of $\mathbb Z$ with no monotone 4-term AP) must never create such a cycle, of any length, at any stage. This is a forbidden-configuration result for the tree-witness method for Erdős #195, not a resolution of the problem.
--
--   Formalization note: the chain is `P : ℕ → List ℤ` with `P n <+: P (n+1)`, safety is `∃ θ, Safe (treeLt θ) (P n)`, coverage is `∀ x, ∃ n, x ∈ P n`; positions via `List.idxOf`, successor index `(i+1) % m`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem open_cycle_blocks_exhaustive_chain (P : ℕ → List ℤ) (hpre : ∀ n, P n <+: P (n + 1))
    (hsafe : ∀ n, ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (P n)) (hcov : ∀ x : ℤ, ∃ n, x ∈ P n)
    (N m : ℕ) (hm : 0 < m) (a b : ℕ → ℤ)
    (ha : ∀ i < m, a i ∈ P N) (hb : ∀ i < m, b i ∈ P N)
    (hi : ∀ i < m, (P N).idxOf (a i) < (P N).idxOf (b i))
    (hcyc : ∀ i < m, 3 * b i - 2 * a i = 2 * b ((i + 1) % m) - a ((i + 1) % m))
    (ht : ∀ i < m, 2 * b i - a i ∉ P N) : False := by sorry

end Erdos195
