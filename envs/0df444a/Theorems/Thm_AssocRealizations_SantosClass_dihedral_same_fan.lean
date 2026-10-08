-- Prove2me | Theorems.Thm_AssocRealizations_SantosClass_dihedral_same_fan
-- name    : AssocRealizations.SantosClass.dihedral_same_fan
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:11.201176+00:00
-- url     : https://prove2.me/theorems/f096312e-e591-46d6-bb84-4ddcef1b1386
-- title:
--   Proof of Corollary 5.7 — dihedral images give isomorphic Santos fans
-- statement:
--   Let $T_1$ be a triangulation of an $(n+3)$-gon, and let a rotation or reflection send it to $T_2$. Relabelling the basis vectors by this polygon symmetry yields a linear isomorphism of the corresponding Santos fans:
--
--   $$
--   T_2=g(T_1)\text{ for a rotation or reflection }g
--   \quad\Longrightarrow\quad F(T_1)\cong_{\mathrm{lin}}F(T_2).
--   $$
--
--   This is the forward implication of Corollary 5.7, for every dimension $n$.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 24, proof of Corollary 5.7, first sentence

import Mathlib
import Definitions.Def_AssocRealizations_SantosClass_Setting

open ChvatalArtGallery.FanPartition

namespace AssocRealizations.SantosClass

theorem dihedral_same_fan (n : ℕ)
    (T₁ T₂ : Finset (Sym2 (Fin (n + 3))))
    (h₁ : IsTriangulation (n + 3) T₁)
    (hdihedral : AssocRealizations.TypesMeet.IsDihedralImage T₁ T₂) :
    AssocRealizations.TypesMeet.NormallyIsomorphic (AssocRealizations.TypesMeet.santosFan T₁) (AssocRealizations.TypesMeet.santosFan T₂) := by sorry

end AssocRealizations.SantosClass
