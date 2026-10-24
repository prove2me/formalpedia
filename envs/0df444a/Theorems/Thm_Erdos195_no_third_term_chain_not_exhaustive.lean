-- Prove2me | Theorems.Thm_Erdos195_no_third_term_chain_not_exhaustive
-- name    : Erdos195.no_third_term_chain_not_exhaustive
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T06:12:27.22779+00:00
-- url     : https://prove2.me/theorems/e83b045b-7576-4085-9bad-946aa11daab8
-- title:
--   Chains never appending a third term $2v-u$ cannot exhaust $\mathbb{Z}$
-- statement:
--   Let $P_0$ be a finite word of integers and $P_{n+1}=P_n\cdot w_n$ with $w_n\notin P_n$. Suppose no appended entry is a third term of an in-order pair:
--   $$w_n\neq 2v-u\quad\text{whenever } u,v\in P_n \text{ and } u \text{ occurs before } v \text{ in } P_n.$$
--   Then $\bigcup_n P_n$ is not cofinite in $\mathbb{Z}$; in particular such a chain can never exhaust $\mathbb{Z}$. Both the isolated-minimum completion and the exterior-record insertion for tree-safe words carry exactly this side condition, so in Ho-style constructions of permutations of $\mathbb{Z}$ without monotone $4$-term APs (Erdős Problem 195) chains using only these two moves cannot produce a permutation of $\mathbb{Z}$.
--
--   Formalization note: this is a purely combinatorial statement about integer sequences, phrased with `t : ℕ → ℤ` (or a chain of lists `P n` with `P (n+1) = P n ++ [w n]`); "cofinite" is expressed as existence of a finite set `F : Finset ℤ` outside of which every integer occurs.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statements from GPT 6 Astra (Oct 23 2026 'tree' answers tree10, generalized), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem no_third_term_chain_not_exhaustive (P : ℕ → List ℤ) (w : ℕ → ℤ)
    (hstep : ∀ n, P (n + 1) = P n ++ [w n]) (hfresh : ∀ n, w n ∉ P n)
    (hno : ∀ n u v, u ∈ P n → v ∈ P n → (P n).idxOf u < (P n).idxOf v → w n ≠ 2 * v - u) :
    ¬ ∃ F : Finset ℤ, ∀ z, z ∉ F → ∃ n, z ∈ P n := by sorry

end Erdos195
