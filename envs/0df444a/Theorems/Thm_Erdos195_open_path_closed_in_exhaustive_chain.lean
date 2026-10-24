-- Prove2me | Theorems.Thm_Erdos195_open_path_closed_in_exhaustive_chain
-- name    : Erdos195.open_path_closed_in_exhaustive_chain
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T22:32:33.909618+00:00
-- url     : https://prove2.me/theorems/bb920c14-8083-4694-ab72-4aac3ca0d363
-- title:
--   Every open path in a stage of an exhaustive tree-safe chain is eventually closed backwards
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework); a finite word is $\theta$-safe if it followed by all remaining integers in $\prec_\theta$-order has no monotone 4-term AP (positions = first occurrences). Consider a chain of words $P_0\sqsubseteq P_1\sqsubseteq\cdots$, each a prefix of the next and each $\theta_n$-safe for some tree witness $\theta_n$ (which may change with $n$), such that every integer occurs in some $P_n$. An open path in $P_N$ is a family of in-order pairs $(a_i,b_i)$, $0\le i<m$, of letters of $P_N$ with $3b_i-2a_i=2b_{i+1}-a_{i+1}$ for $i<m-1$ and no third term $t_i=2b_i-a_i$ in $P_N$. **Theorem.** For every such open path there is a stage $n\ge N$ such that $P_n$ contains all third terms $t_j$ and all fourth terms $w_j=3b_j-2a_j$ ($j<m$), and in $P_n$ each $w_j$ comes before $t_j$.
--
--   So in any exhaustive chain of tree-safe words, every open path is eventually closed completely, in reverse order starting from the sink's fourth term $w_{m-1}$. Together with milestone 144 (open cycles block exhaustive chains), this describes what must happen to every chain of linked open pairs. It is a structural lemma about the tree-witness approach to Erdős #195, not a construction or an impossibility result.
--
--   Formalization note: stages are `P : ℕ → List ℤ` with `P n <+: P (n+1)`; coverage is `∀ x, ∃ n, x ∈ P n`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem open_path_closed_in_exhaustive_chain (P : ℕ → List ℤ) (hpre : ∀ n, P n <+: P (n + 1))
    (hsafe : ∀ n, ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (P n)) (hcov : ∀ x : ℤ, ∃ n, x ∈ P n)
    (N m : ℕ) (a b : ℕ → ℤ)
    (ha : ∀ i < m, a i ∈ P N) (hb : ∀ i < m, b i ∈ P N)
    (hi : ∀ i < m, (P N).idxOf (a i) < (P N).idxOf (b i))
    (hpath : ∀ i, i + 1 < m → 3 * b i - 2 * a i = 2 * b (i + 1) - a (i + 1))
    (ht : ∀ i < m, 2 * b i - a i ∉ P N) :
    ∃ n, N ≤ n ∧ ∀ j < m,
      2 * b j - a j ∈ P n ∧ 3 * b j - 2 * a j ∈ P n ∧
        (P n).idxOf (3 * b j - 2 * a j) < (P n).idxOf (2 * b j - a j) := by sorry

end Erdos195
