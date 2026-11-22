-- Prove2me | Theorems.Thm_CubicSurface27_cayley_salmon_core
-- name    : CubicSurface27.cayley_salmon_core
-- status  : Open
-- author  : @LG
-- created : 2026-11-22T01:31:55.255332+00:00
-- url     : https://prove2.me/theorems/43ce0a91-66e7-424e-ab0e-7d8bf16666bf
-- title:
--   Cayley-Salmon core lemma
-- statement:
--   This is the core statement of the Cayley-Salmon theorem, isolated as a reusable lemma. It asserts that any smooth cubic form $F$ over the complex numbers defines a cubic surface containing exactly 27 lines. Let $V(F) \subset \mathbb{P}^3$ be the projective surface associated with $F$. The lines on $V(F)$ correspond to the 2-dimensional linear subspaces of $\mathbb{C}^4$ on which $F$ vanishes identically. The cardinality of the set of such subspaces is exactly 27. $$ \#\{\text{lines on } V(F)\} = 27 $$
--
--   **Formalization Note.** The count is represented by the natural cardinality `Set.ncard (linesOf F)`, and the smoothness of the cubic is captured by the predicate `IsSmoothCubic F`.
-- source:
--   Jack Huizenga, answer to 'In Algebraic Geometry, why are there exactly 27 straight lines on a smooth cubic surface?', Quora.

import Mathlib
import Definitions.Def_cubic_surface_27_layer

namespace CubicSurface27

theorem cayley_salmon_core (F : MvPolynomial (Fin 4) ℂ)
    (hF : IsCubicForm F) (hsm : IsSmoothCubic F) :
    (linesOf F).ncard = 27 := by sorry

end CubicSurface27
