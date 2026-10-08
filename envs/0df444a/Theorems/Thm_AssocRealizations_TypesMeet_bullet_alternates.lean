-- Prove2me | Theorems.Thm_AssocRealizations_TypesMeet_bullet_alternates
-- name    : AssocRealizations.TypesMeet.bullet_alternates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:27:58.93135+00:00
-- url     : https://prove2.me/theorems/b45f8eda-f140-4c84-bdba-6144b1e311f4
-- title:
--   Theorem 6.1 proof, third bullet — consecutive chain edges have different apices
-- statement:
--   Under the same assumptions, there cannot be two distinct triangles $abp$ and $bcp$ in $T$ such that $ab$ and $bc$ are consecutive boundary edges of one sign chain and both triangles have apex $p$ on the other chain:
--
--   $$\neg\exists a,b,c,p:\ ab,bc\text{ are chain edges and }abp,bcp\in\operatorname{Triangles}(T).$$
--
--   This rules out two consecutive turns to the same side in the triangulation's dual path.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, pp. 28–29, proof of Theorem 6.1, third bullet

import Mathlib
import Definitions.Def_AssocRealizations_TypesMeet_Setting

namespace AssocRealizations.TypesMeet

open ChvatalArtGallery.FanPartition

theorem bullet_alternates (n : ℕ) (σ : Fin (n - 1) → Bool)
    (T : Finset (Sym2 (Fin (n + 3))))
    (hT : IsTriangulation (n + 3) T) (hB : OppositeSignB σ T) :
    ¬ ∃ a b c p : Fin (n + 3),
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ p ≠ a ∧ p ≠ b ∧ p ≠ c ∧
      IsBoundaryEdge s(a, b) ∧ IsBoundaryEdge s(b, c) ∧
      hlSignPos σ a = hlSignPos σ b ∧ hlSignPos σ b = hlSignPos σ c ∧
      ({a, b, p} : Finset (Fin (n + 3))) ∈ triangles (n + 3) T ∧
      ({b, c, p} : Finset (Fin (n + 3))) ∈ triangles (n + 3) T := by sorry
end AssocRealizations.TypesMeet
