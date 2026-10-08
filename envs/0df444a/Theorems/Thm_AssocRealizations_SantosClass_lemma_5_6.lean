-- Prove2me | Theorems.Thm_AssocRealizations_SantosClass_lemma_5_6
-- name    : AssocRealizations.SantosClass.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:28.600585+00:00
-- url     : https://prove2.me/theorems/b1cc1105-cc86-4fc6-a8c2-1eb8381e188d
-- title:
--   Lemma 5.6 — a triangulation is determined by its seed and flip insertions
-- statement:
--   Let $n\ge2$. For a triangulation $T$ of an $(n+3)$-gon, let $B_T$ consist of its $n$ diagonals and the $n$ diagonals that can be introduced by one flip. Then
--
--   $$
--   T_1\ne T_2\quad\Longrightarrow\quad B_{T_1}\ne B_{T_2}.
--   $$
--
--   Thus the set visible from the parallel facet pairs identifies the seed triangulation. The restriction $n\ge2$ is essential: the two triangulations of a quadrilateral have the same $B_T$.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, pp. 23–24, Lemma 5.6

import Mathlib
import Definitions.Def_AssocRealizations_SantosClass_Setting

open ChvatalArtGallery.FanPartition

namespace AssocRealizations.SantosClass

theorem lemma_5_6 (n : ℕ) (hn : 2 ≤ n)
    (T₁ T₂ : Finset (Sym2 (Fin (n + 3))))
    (h₁ : IsTriangulation (n + 3) T₁)
    (h₂ : IsTriangulation (n + 3) T₂)
    (hne : T₁ ≠ T₂) : bSet T₁ ≠ bSet T₂ := by sorry

end AssocRealizations.SantosClass
