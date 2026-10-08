-- Prove2me | Theorems.Thm_AssocRealizations_TypesMeet_three_properties_snake
-- name    : AssocRealizations.TypesMeet.three_properties_snake
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:28:21.761738+00:00
-- url     : https://prove2.me/theorems/fd4f5f24-a604-4cb8-8a5f-e371725082fb
-- title:
--   Theorem 6.1 proof — the three triangle properties force the snake
-- statement:
--   Let $T$ triangulate the polygon. Suppose each triangle has a same-sign boundary edge, each triangle meets both sign chains, and no two consecutive boundary edges in one chain have triangles with the same apex. Then $T$ is a rotation or reflection of the fixed alternating snake triangulation:
--
--   $$T=g(\operatorname{snake}_n)\quad\text{for some dihedral symmetry }g.$$
--
--   These are the three properties stated in the proof of Theorem 6.1. **Formalization Note** The source identifies the snake after a without-loss-of-generality relabelling; the statement restores that dihedral relabelling.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 29, proof of Theorem 6.1, sentence following the third bullet

import Mathlib
import Definitions.Def_AssocRealizations_TypesMeet_Setting

namespace AssocRealizations.TypesMeet

open ChvatalArtGallery.FanPartition

theorem three_properties_snake (n : ℕ) (σ : Fin (n - 1) → Bool)
    (T : Finset (Sym2 (Fin (n + 3))))
    (hT : IsTriangulation (n + 3) T)
    (hpath : ∀ t ∈ triangles (n + 3) T,
      ∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧
        IsBoundaryEdge s(a, b) ∧ hlSignPos σ a = hlSignPos σ b)
    (hseparates : ∀ t ∈ triangles (n + 3) T,
      ¬ ∃ sign : Bool, ∀ p ∈ t, hlSignPos σ p = sign)
    (halternates : ¬ ∃ a b c p : Fin (n + 3),
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ p ≠ a ∧ p ≠ b ∧ p ≠ c ∧
      IsBoundaryEdge s(a, b) ∧ IsBoundaryEdge s(b, c) ∧
      hlSignPos σ a = hlSignPos σ b ∧ hlSignPos σ b = hlSignPos σ c ∧
      ({a, b, p} : Finset (Fin (n + 3))) ∈ triangles (n + 3) T ∧
      ({b, c, p} : Finset (Fin (n + 3))) ∈ triangles (n + 3) T) :
    IsDihedralImage (snake n) T := by sorry
end AssocRealizations.TypesMeet
