-- Prove2me | Theorems.Thm_AssocRealizations_SantosClass_lemma_2_2
-- name    : AssocRealizations.SantosClass.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:12.71862+00:00
-- url     : https://prove2.me/theorems/81c34601-b19a-4c9b-a5ca-78b25d7b8b26
-- title:
--   Lemma 2.2 — automorphisms of the associahedron are polygon symmetries
-- statement:
--   Let $\pi$ be a bijection of unordered vertex pairs of a convex $(n+3)$-gon. Suppose $\pi$ carries diagonals bijectively to diagonals and, for every two diagonals, preserves whether they cross. Then there is a rotation or reflection $g$ of the polygon such that
--
--   $$
--   \pi(e)=g(e)\qquad\text{for every diagonal }e.
--   $$
--
--   This is the diagonal form of the paper's face-lattice automorphism lemma. It identifies the only possible combinatorial action induced by a normal-fan isomorphism.
--
--   **Formalization Note** The printed second sentence, the order of the automorphism group for $n\ge2$, is a consequence and is not a separate target here. The diagonal action in the first sentence also covers $n=0,1$.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 6, Lemma 2.2

import Mathlib
import Definitions.Def_AssocRealizations_SantosClass_Setting

open ChvatalArtGallery.FanPartition

namespace AssocRealizations.SantosClass

theorem lemma_2_2 (n : ℕ)
    (π : Sym2 (Fin (n + 3)) ≃ Sym2 (Fin (n + 3)))
    (hdiag : ∀ e, IsDiagonal e ↔ IsDiagonal (π e))
    (hcross : ∀ e f, IsDiagonal e → IsDiagonal f →
      (Crosses e f ↔ Crosses (π e) (π f))) :
    ∃ r : Fin (n + 3), ∃ refl : Bool,
      ∀ e, IsDiagonal e → π e = Sym2.map (AssocRealizations.TypesMeet.dihedral r refl) e := by sorry

end AssocRealizations.SantosClass
