-- Prove2me | Theorems.Thm_AssocRealizations_HLClass_lemma_2_2
-- name    : AssocRealizations.HLClass.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:30.945722+00:00
-- url     : https://prove2.me/theorems/aa52676e-7051-4975-adae-7ef72f437589
-- title:
--   Lemma 2.2 — crossing-preserving bijections of the diagonals are dihedral symmetries of the (n+3)-gon
-- statement:
--   Let $n \ge 0$ and let $\pi$ be a bijection of the set of diagonals of a convex $(n+3)$-gon onto itself such that, for all diagonals $\delta, \delta'$,
--   $$\delta \text{ crosses } \delta' \iff \pi(\delta) \text{ crosses } \pi(\delta').$$
--   Then there is a dihedral symmetry $g$ of the $(n+3)$-gon (a rotation $i \mapsto r+i$ or a reflection $i \mapsto r-i$, indices mod $n+3$) such that $\pi(\delta) = g(\delta)$ for every diagonal $\delta$. If $n \ge 2$, this symmetry is unique.
--
--   An automorphism of the face lattice of the associahedron $\mathrm{Ass}_n$ permutes its facets, which correspond to the diagonals, and two facets intersect iff their diagonals do not cross; so this is Lemma 2.2 of the paper: all automorphisms of the face lattice of $\mathrm{Ass}_n$ are induced by symmetries of the $(n+3)$-gon, and for $n \ge 2$ the automorphism group is the dihedral group of order $2n+6$ (existence of $g$ is the first sentence, uniqueness the second). In the classification it converts a normal isomorphism between two associahedra into a symmetry of the polygon.
--
--   **Formalization Note** The statement is on diagonals rather than on the face lattice, as in the paper's own proof. The threshold $n \ge 2$ applies only to uniqueness, as on the page; for $n=1$ the square has two diagonals and eight symmetries, so uniqueness fails.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 6, Lemma 2.2

import Mathlib
import Definitions.Def_AssocRealizations_HLClass_Setting

namespace AssocRealizations.HLClass

open ChvatalArtGallery.FanPartition

/-- Lemma 2.2 (p. 6), stated on diagonals: every crossing-preserving bijection of the diagonals
is induced by a dihedral symmetry. For `n ≥ 2`, this symmetry is unique, giving the group of
order `2n + 6`. -/
theorem lemma_2_2 (n : ℕ) (π : Sym2 (Fin (n + 3)) → Sym2 (Fin (n + 3)))
    (hπ : Set.BijOn π {e | IsDiagonal e} {e | IsDiagonal e})
    (hcross : ∀ e f : Sym2 (Fin (n + 3)), IsDiagonal e → IsDiagonal f →
      (Crosses e f ↔ Crosses (π e) (π f))) :
    (∃ g : Fin (n + 3) × Bool,
      ∀ e : Sym2 (Fin (n + 3)), IsDiagonal e →
        π e = Sym2.map (AssocRealizations.TypesMeet.dihedral g.1 g.2) e) ∧
    (2 ≤ n → ∃! g : Fin (n + 3) × Bool,
      ∀ e : Sym2 (Fin (n + 3)), IsDiagonal e →
        π e = Sym2.map (AssocRealizations.TypesMeet.dihedral g.1 g.2) e) := by sorry

end AssocRealizations.HLClass
