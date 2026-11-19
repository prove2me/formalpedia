-- Prove2me | Theorems.Thm_Erdos195_specified_first_safe_order
-- name    : Erdos195.specified_first_safe_order
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-18T11:55:00.901198+00:00
-- url     : https://prove2.me/theorems/93ef7568-efb2-4190-a692-11ca565a121e
-- title:
--   Specified-first-entry ordering: every finite set has a SAFE ordering beginning at any prescribed element
-- statement:
--   A tree witness is a function $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ on the nodes $(k,r)$ of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=1\Leftrightarrow\theta(k,\,x\bmod 2^k)=1$. A finite word $L$ is $\theta$-safe if the completion “letters of $L$ in order, then all remaining integers in $\prec_\theta$-order” contains no monotone $4$-term arithmetic progression. Positions are first occurrences.
--
--   **Theorem.** Let $X\subset\mathbb Z$ be a finite set and $p\in X$. Then there is a duplicate-free list $L$ whose set of entries is exactly $X$, whose first entry is $p$, and which is tree-safe for some witness $\theta$.
--
--   The proof sorts $X$ by the tree order that prefers the two’s-complement bits of $p$ at every level, so that $p$ is the least element. This order has no monotone $3$-term AP, hence $L$ has no in-order $3$-AP, and the continuation clause of `exists_treeLt_safe_iff` holds. Every open in-order pair $(a,b)$ has $\mathrm{bit}_k(a)=\mathrm{bit}_k(p)$ and therefore forces the complementary bit of $b$; all open pairs at a given level agree, so the no-conflict clause also holds.
--
--   This is the first-entry dual of the already-proved `specified_last_safe_order`, and is the elementary ordering lemma used in the safe-word composition analysis. It is not the unrestricted extension lemma, does not claim that an arbitrary prescribed prefix can be preserved, and does not settle Erdős #195.
--
--   **Formalization Note** Safety is official `Safe (treeLt θ)`. The first-entry hypothesis is `L.head? = some p`. The list is required to be `Nodup` and to have the same membership as the finite set $X`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); derived from analysis relayed by Ethan Cheung, hand-checked against the official Safe / treeLt / exists_treeLt_safe_iff / treeLt_order_props definitions, Lean-verified.

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem specified_first_safe_order (X : Finset ℤ) (p : ℤ) (hp : p ∈ X) :
    ∃ L : List ℤ, L.Nodup ∧ (∀ x, x ∈ L ↔ x ∈ X) ∧ L.head? = some p ∧
      ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) L := by sorry

end Erdos195
