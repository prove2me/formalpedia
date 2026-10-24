-- Prove2me | Theorems.Thm_Erdos195_mixed_batches_recur
-- name    : Erdos195.mixed_batches_recur
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T18:27:10.689092+00:00
-- url     : https://prove2.me/theorems/acd6171e-ecd8-4847-975b-a5b884cd7041
-- title:
--   Cofinal SAFE chains need infinitely many genuinely mixed-parity batches (tree orders)
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression; $Q$ is SAFE if it is $\theta$-safe for some tree witness $\theta$.
--
--   **Theorem (cofinal SAFE chains need infinitely many genuinely mixed batches).** Let $Q_0\preceq Q_1\preceq Q_2\preceq\cdots$ be duplicate-free SAFE words, each a prefix of the next (each stage may use its own witness), whose union is all of $\mathbb Z$. Then for every $J$ there is $j\ge J$ such that the batch of letters of $Q_{j+1}$ not in $Q_j$ contains integers of both parities.
--
--   In other words, an exhaustive construction of a permutation of $\mathbb Z$ through SAFE stages can never eventually proceed by single-parity batches; equivalently it cannot eventually factor into finitely many monochromatic SAFE sub-batches per step. This is a necessary condition on any successful stagewise construction for Erdős Problem 195 in the tree-witness framework, not a construction or an impossibility proof. Theorem of GPT 6 Astra.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; lemma of GPT 6 Astra; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem mixed_batches_recur (Q : ℕ → List ℤ)
    (hS : ∀ j, ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (Q j))
    (hnd : ∀ j, (Q j).Nodup) (hpre : ∀ j, Q j <+: Q (j + 1))
    (hcov : ∀ x : ℤ, ∃ j, x ∈ Q j) :
    ∀ J, ∃ j ≥ J, ∃ x ∈ Q (j + 1), ∃ x' ∈ Q (j + 1), x ∉ Q j ∧ x' ∉ Q j ∧ x % 2 ≠ x' % 2 := by sorry

end Erdos195
