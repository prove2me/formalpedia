-- Prove2me | Theorems.Thm_CountOrderings_NFree_lemma_2_2
-- name    : CountOrderings.NFree.lemma_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:57:25.028889+00:00
-- url     : https://prove2.me/theorems/51b28376-9d11-4ed9-a926-a50444357c6d
-- title:
--   Lemma 2.2 — hook-length formula for rooted tree posets
-- statement:
--   Let $T$ be a finite poset whose Hasse diagram is a rooted tree: $T$ has a minimum element (the root), and every other element covers exactly one element. For $v \in T$ let $T_v = \{u \in T \mid v \preceq u\}$ be the subtree rooted at $v$. Then the number of linear extensions of $T$ is
--   $$\#\mathrm{LE}(T) = \frac{|T|!}{\prod_{v \in T} |T_v|} .$$
--
--   This classical hook-length formula is the counting tool behind every reduction of the paper: fixing the order of the original elements turns the remaining constraints into a tree poset, whose linear extensions it counts in closed form (§3, §6).
--
--   **Formalization Note.** The identity is stated in $\mathbb{Q}$; every $|T_v| \ge 1$, so the quotient is an honest one. Covers, $\#\mathrm{LE}$, rooted tree posets and $|T_v|$ are those of `CountOrderings.NFree.Poset`.
--
--   Differences from the source:
--   - encoding: "a poset whose Hasse diagram is a rooted tree (root = minimum, order increasing away from it)" → a finite poset with a least element in which every other element covers exactly one element; reason: for finite posets the two descriptions are equivalent (the Hasse diagram is then an out-tree from the root).
--   - encoding: #LE(T) = |T|!/∏|T_v| as a quotient → the same identity in ℚ with #LE(T) cast from ℕ; reason: every |T_v| ≥ 1, same value.
-- source:
--   Arenas, Schild and Subercaseaux, Hardness of Counting Orderings: Taking Gadget Amplification to the Limit, STOC 2027 submission, p. 8 (PDF p. 9), Lemma 2.2 and footnote 2; proof in Appendix A.1, pp. 27–28 (PDF pp. 28–29)

import Mathlib
import Definitions.Def_CountOrderings_NFree_Poset

namespace CountOrderings.NFree

theorem lemma_2_2 (T : Type) [PartialOrder T] [Fintype T] (hT : IsRootedTreePoset T) :
    (numLinExt T : ℚ) =
      ((Fintype.card T).factorial : ℚ) / ∏ v : T, (upSetCard v : ℚ) := by sorry

end CountOrderings.NFree
