-- Prove2me | Theorems.Thm_FinitePresentation_isFinitelyPresented_of_finiteIndex
-- name    : FinitePresentation.isFinitelyPresented_of_finiteIndex
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T20:24:32.367701+00:00
-- url     : https://prove2.me/theorems/b2e07ba7-9423-4e5d-8685-1a2cf2c0cfe5
-- title:
--   A group with a finitely presented subgroup of finite index is finitely presented
-- statement:
--   Let $G$ be a group and $H \le G$ a subgroup of finite index. If $H$ is finitely presented, then so is $G$:
--
--   $$[G : H] < \infty \ \text{ and } \ H \text{ finitely presented} \implies G \text{ finitely presented}.$$
--
--   The subgroup $H$ need not be normal, so this generalizes the statement that an extension of a finitely presented group by a finite group is finitely presented. With the converse (a finite-index subgroup of a finitely presented group is finitely presented, by Reidemeister–Schreier), it shows that finite presentability is invariant under commensurability; it is a special case of its invariance under quasi-isometry.
--
--   **Formalization Note.** Finite presentation is Mathlib's `Group.IsFinitelyPresented`: a surjection from the free group on `Fin n` whose kernel is the normal closure of a finite set. Finite index is `Subgroup.FiniteIndex` (nonzero index), and $H$ carries its subgroup group structure.
-- source:
--   C. Löh, Geometric Group Theory: An Introduction, draft of the book (Universitext, Springer, 2017), p. 150, Example 5.6.7: "Being finitely presented is a geometric property of groups", that is, invariant under quasi-isometry (Definition 5.6.6, same page), citing Bridson and Haefliger, Proposition I.8.24; with p. 137, Corollary 5.4.5, "Finite index subgroups of finitely generated groups are finitely generated and quasi-isometric to the ambient group (via the inclusion map)", this gives the statement, since G is finitely generated when H is; https://loeh.app.uni-regensburg.de/ggt_book/ggt_book_draft.pdf. The published book: https://doi.org/10.1007/978-3-319-72254-2

import Mathlib

namespace FinitePresentation

theorem isFinitelyPresented_of_finiteIndex {G : Type*} [Group G] (H : Subgroup G)
    [H.FiniteIndex] [Group.IsFinitelyPresented H] : Group.IsFinitelyPresented G := by
  sorry

end FinitePresentation
