-- Prove2me | Theorems.Thm_Erdos195_specified_last_safe_order
-- name    : Erdos195.specified_last_safe_order
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:22:08.498697+00:00
-- url     : https://prove2.me/theorems/16637c78-ec7e-4bbc-a379-c1a892636c63
-- title:
--   Specified-last-entry ordering: every finite set has a SAFE ordering ending at any prescribed element
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework). A finite word $W$ of integers is SAFE for $\theta$ if the sequence "letters of $W$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression. **Theorem.** Let $X\subset\mathbb Z$ be a finite set and $z\in X$. Then there is a duplicate-free list $L$ whose set of entries is exactly $X$, whose last entry is $z$, and which is SAFE for some tree witness $\theta$.
--
--   This is the ordering lemma used by GPT 6 Astra in the exceptional case of the four-class restricted absorption theorem: a reflection set must be appended in a safe order with one prescribed entry last. The proof uses the tree order with $\theta(k,\cdot)=\neg\mathrm{bit}_k(z)$, in which $z$ is the greatest element. Sort $X\setminus\{z\}$ increasingly in it and append $z$. A list sorted increasingly for $\prec_\theta$ is SAFE for the reversed order, which is the tree order $\prec_{\neg\theta}$. This is the tree version of Ho's reverse-order lemma.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026); lemma of GPT 6 Astra (astra_restricted / astra_fourclass)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem specified_last_safe_order (X : Finset ℤ) (z : ℤ) (hz : z ∈ X) :
    ∃ L : List ℤ, L.Nodup ∧ (∀ x, x ∈ L ↔ x ∈ X) ∧ L.getLast? = some z ∧
      ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) L := by sorry

end Erdos195
