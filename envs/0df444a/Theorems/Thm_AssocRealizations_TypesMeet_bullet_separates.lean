-- Prove2me | Theorems.Thm_AssocRealizations_TypesMeet_bullet_separates
-- name    : AssocRealizations.TypesMeet.bullet_separates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:28:09.477491+00:00
-- url     : https://prove2.me/theorems/04cf7a3d-dd32-4b65-9a5d-dac6441c099b
-- title:
--   Theorem 6.1 proof, second bullet — triangles meet both chains
-- statement:
--   Under the same triangulation and opposite-sign assumptions, no triangle of $T$ has all three vertices on one sign chain:
--
--   $$\forall t\in\operatorname{Triangles}(T),\quad
--   eg\exists s\in\{+,-\}\ \forall p\in t,\ \operatorname{sign}(p)=s.$$
--
--   Together with the first bullet, each triangle has two vertices on one chain and its third vertex on the other.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 28, proof of Theorem 6.1, second bullet

import Mathlib
import Definitions.Def_AssocRealizations_TypesMeet_Setting

namespace AssocRealizations.TypesMeet

open ChvatalArtGallery.FanPartition

theorem bullet_separates (n : ℕ) (σ : Fin (n - 1) → Bool)
    (T : Finset (Sym2 (Fin (n + 3))))
    (hT : IsTriangulation (n + 3) T) (hB : OppositeSignB σ T) :
    ∀ t ∈ triangles (n + 3) T,
      ¬ ∃ sign : Bool, ∀ p ∈ t, hlSignPos σ p = sign := by sorry
end AssocRealizations.TypesMeet
