-- Prove2me | Theorems.Thm_AssocRealizations_TypesMeet_bullet_path
-- name    : AssocRealizations.TypesMeet.bullet_path
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:28:11.143103+00:00
-- url     : https://prove2.me/theorems/d346ea25-2960-428b-a81d-6b0eea100cba
-- title:
--   Theorem 6.1 proof, first bullet — every triangle has a chain edge
-- statement:
--   Suppose $T$ is a triangulation and every diagonal of $T$, together with every diagonal inserted by one flip, joins vertices of opposite Hohlweg–Lange signs. Then every triangle of $T$ contains a boundary edge whose endpoints lie on the same sign chain:
--
--   $$\forall t\in\operatorname{Triangles}(T),\ \exists a\ne b\in t:\ \{a,b\}\text{ is a boundary edge and }\operatorname{sign}(a)=\operatorname{sign}(b).$$
--
--   This is the first structural property used to identify the snake triangulation.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 28, proof of Theorem 6.1, first bullet

import Mathlib
import Definitions.Def_AssocRealizations_TypesMeet_Setting

namespace AssocRealizations.TypesMeet

open ChvatalArtGallery.FanPartition

theorem bullet_path (n : ℕ) (σ : Fin (n - 1) → Bool)
    (T : Finset (Sym2 (Fin (n + 3))))
    (hT : IsTriangulation (n + 3) T) (hB : OppositeSignB σ T) :
    ∀ t ∈ triangles (n + 3) T,
      ∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧
        IsBoundaryEdge s(a, b) ∧ hlSignPos σ a = hlSignPos σ b := by sorry
end AssocRealizations.TypesMeet
