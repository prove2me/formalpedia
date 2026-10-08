-- Prove2me | Theorems.Thm_AssocRealizations_SantosClass_corollary_5_7
-- name    : AssocRealizations.SantosClass.corollary_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:29.437271+00:00
-- url     : https://prove2.me/theorems/0e6c5404-2e13-4f19-b985-d7ba392269ad
-- title:
--   Corollary 5.7 — Santos fans are classified by seed triangulations modulo dihedral symmetry
-- statement:
--   Let $T_1,T_2$ be triangulations of a convex $(n+3)$-gon. Write $F(T)$ for the Santos normal fan constructed from the seed $T$. Then
--
--   $$
--   F(T_1)\cong_{\mathrm{lin}}F(T_2)
--   \quad\Longleftrightarrow\quad
--   T_2=g(T_1)\text{ for some rotation or reflection }g.
--   $$
--
--   Thus dihedral orbits of seed triangulations, and no coarser identification, classify the Santos associahedra by normal isomorphism. This is the mission goal.
--
--   **Formalization Note** The fan is the collection of cones spanned by the explicit Santos vectors over all noncrossing diagonal sets. The two seed spaces have separately indexed bases, and the linear isomorphism compares them without a chosen numbering.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 24, Corollary 5.7

import Mathlib
import Definitions.Def_AssocRealizations_SantosClass_Setting

open ChvatalArtGallery.FanPartition

namespace AssocRealizations.SantosClass

theorem corollary_5_7 (n : ℕ)
    (T₁ T₂ : Finset (Sym2 (Fin (n + 3))))
    (h₁ : IsTriangulation (n + 3) T₁)
    (h₂ : IsTriangulation (n + 3) T₂) :
    AssocRealizations.TypesMeet.NormallyIsomorphic (AssocRealizations.TypesMeet.santosFan T₁) (AssocRealizations.TypesMeet.santosFan T₂) ↔
      AssocRealizations.TypesMeet.IsDihedralImage T₁ T₂ := by sorry

end AssocRealizations.SantosClass
