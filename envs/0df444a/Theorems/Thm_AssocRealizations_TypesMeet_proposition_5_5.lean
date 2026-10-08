-- Prove2me | Theorems.Thm_AssocRealizations_TypesMeet_proposition_5_5
-- name    : AssocRealizations.TypesMeet.proposition_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:28:02.918635+00:00
-- url     : https://prove2.me/theorems/b73d1266-fc3a-4949-9cc1-fffac3bf6b00
-- title:
--   Proposition 5.5 — parallel pairs in the Santos fan
-- statement:
--   Let $T_0$ be a triangulation and let $e,f$ be distinct diagonals. Their type II facet normals point in opposite directions exactly when one is a seed diagonal and the other is the diagonal inserted by flipping it:
--
--   $$v^{II}_{e}\parallel_{-}v^{II}_{f}\iff
--   (e\in T_0\ \text{and}\ T_0-e+f\text{ triangulates})\ \text{or}(f\in T_0\ \text{and}\ T_0-f+e\text{ triangulates}).$$
--
--   It enumerates all parallel-facet pairs of the Santos associahedron. **Formalization Note** Both inputs are restricted to diagonals, because only diagonals index facets; this avoids treating the zero ray of a boundary edge as a facet normal.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 23, Proposition 5.5

import Mathlib
import Definitions.Def_AssocRealizations_TypesMeet_Setting

namespace AssocRealizations.TypesMeet

open ChvatalArtGallery.FanPartition

theorem proposition_5_5 (n : ℕ)
    (T₀ : Finset (Sym2 (Fin (n + 3))))
    (hT : IsTriangulation (n + 3) T₀)
    (e f : Sym2 (Fin (n + 3))) (he : IsDiagonal e) (hf : IsDiagonal f)
    (hne : e ≠ f) :
    Opposite (santosVec T₀ e) (santosVec T₀ f) ↔
      (e ∈ T₀ ∧ IsTriangulation (n + 3) (insert f (T₀.erase e))) ∨
      (f ∈ T₀ ∧ IsTriangulation (n + 3) (insert e (T₀.erase f))) := by sorry
end AssocRealizations.TypesMeet
