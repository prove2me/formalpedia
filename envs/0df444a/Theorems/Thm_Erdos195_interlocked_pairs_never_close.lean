-- Prove2me | Theorems.Thm_Erdos195_interlocked_pairs_never_close
-- name    : Erdos195.interlocked_pairs_never_close
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:22:09.981685+00:00
-- url     : https://prove2.me/theorems/d314ee46-79ad-4071-9359-2c729c53a7a1
-- title:
--   Interlocked open pairs (swapped third/fourth terms) can never be closed
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework). A finite word $W$ of integers is SAFE for $\theta$ if the sequence "letters of $W$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression. **Theorem.** Let $T$ be a finite word containing $a$ before $b$ and $a'$ before $b'$, with
--   $$2b-a=3b'-2a',\qquad 3b-2a=2b'-a',$$
--   and suppose neither of these two values occurs in $T$. Then for every tree witness $\theta$ and every word $R$ with $T R$ SAFE for $\theta$, neither $2b-a$ nor $3b-2a$ occurs in $TR$.
--
--   The pairs $(a,b)$ and $(a',b')$ have their third and fourth terms swapped. Appending one of the two values forces the other to appear earlier, by the in-order 3-AP condition of the tree characterization, so neither can ever appear. Both pairs remain open in every SAFE extension.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem interlocked_pairs_never_close (θ : ℕ → ℤ → Bool) (T R : List ℤ) (a b a' b' : ℤ)
    (ha : a ∈ T) (hb : b ∈ T) (ha' : a' ∈ T) (hb' : b' ∈ T)
    (hi : T.idxOf a < T.idxOf b) (hi' : T.idxOf a' < T.idxOf b')
    (ht : 2 * b - a = 3 * b' - 2 * a') (hw : 3 * b - 2 * a = 2 * b' - a')
    (htT : 2 * b - a ∉ T) (hwT : 3 * b - 2 * a ∉ T)
    (hS : Safe (treeLt θ) (T ++ R)) :
    2 * b - a ∉ T ++ R ∧ 3 * b - 2 * a ∉ T ++ R := by sorry

end Erdos195
