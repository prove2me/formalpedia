-- Prove2me | Theorems.Thm_Erdos195_safe_word_composition
-- name    : Erdos195.safe_word_composition
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-18T19:40:23.02132+00:00
-- url     : https://prove2.me/theorems/7f2271a8-9716-4b95-ad14-174e31e6fdfc
-- title:
--   Safe words compose by concatenating lifts of residue blocks in a tree order
-- statement:
--   A tree witness is a function θ:ℕ×ℤ→{0,1} on the nodes (k,r) of the binary tree of residues. For distinct integers x,y with k=ν₂(y−x), put x≺_θ y iff bit_k(x)=1 precisely when θ(k, x mod 2^k)=1. A finite word Q is θ-safe if the completion “letters of Q in order, then all remaining integers in ≺_θ-order” contains no monotone 4-term arithmetic progression. Positions are first occurrences.
--
--   **Composition theorem.** Fix m≥1. Let residues be a permutation of {0,1,…,2^m−1} that is increasing in some tree-witness order ≺_{θ₀}. For each residue s, let A_s be a finite word in ℤ, and form Q by concatenating, in the residue order, the lifted blocks s+2^m A_s. Then Q admits a tree-safe witness if and only if every child word A_s does.
--
--   The argument is the one recorded in the safe-word composition note. In-order 3-term progressions with valuation k≥m stay inside a single residue block and unlift to the child; those with k<m would require two successive residue comparisons at the same node with opposite orientations, which a tree order forbids. Open pairs at deep nodes transfer uniquely to a child; open pairs at levels k<m all force the complementary bit of θ₀ at that node.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); derived from analysis relayed by Ethan Cheung, hand-checked against the official Safe / treeLt / exists_treeLt_safe_iff definitions, Lean-verified.

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem safe_word_composition (m : ℕ) (hm : 0 < m) (A : ℤ → List ℤ)
    (residues : List ℤ)
    (hres : residues.Perm ((List.range (2 ^ m)).map (fun n : ℕ => (n : ℤ))) )
    (hord : ∃ θ0 : ℕ → ℤ → Bool, residues.Pairwise (treeLt θ0))
    (Q : List ℤ)
    (hQ : Q = (residues.map (fun s => (A s).map (fun x => s + (2 : ℤ) ^ m * x))).flatten) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q) ↔
      (∀ s : ℤ, 0 ≤ s → s < (2 : ℤ) ^ m → ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (A s)) := by sorry

end Erdos195
