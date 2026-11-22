-- Prove2me | Theorems.Thm_CubicSurface27_smooth_implies_transverse
-- name    : CubicSurface27.smooth_implies_transverse
-- status  : Proved
-- author  : @LG
-- created : 2026-11-22T01:53:43.10039+00:00
-- url     : https://prove2.me/theorems/306ba9a2-61b7-4e85-800c-b0d84841e3c9
-- title:
--   If $X$ is smooth, then $s_F$ has transverse zeroes
-- statement:
--   If $X$ is smooth, then the section $s_F$ has transverse zeroes.
--
--   Let $F$ be a homogeneous cubic polynomial in four variables over $\mathbb{C}$, and let $X=V(F)\subset\mathbb{P}^3$ be smooth: at every nonzero point of the affine cone, some partial derivative of $F$ is nonzero. Let $s_F$ be the section of $\mathrm{Sym}^3 S^*$ on the Grassmannian $\mathrm{Gr}(2,4)$ obtained by restricting $F$ to lines. Then $s_F$ has transverse zeroes. At every line $W\subset X$, the derivative
--   $$
--   ds_F:T_W\mathrm{Gr}(2,4)\longrightarrow E_W
--   $$
--   is an isomorphism.
--
--   This is the first sentence of the source's final theorem. Smoothness is essential: a singular cubic may contain a positive-dimensional family of lines, or an isolated line at which $s_F$ fails to meet the zero section transversely. The count of $27$ lines is not part of this statement.
--
--   **Formalization Note.** Smoothness is `IsSmoothCubic` and transverse zeroes are `HasTransverseZeroes`. The Jacobian criterion is the one fixed by `IsSmoothCubic`.
-- source:
--   Jack Huizenga, answer to "In Algebraic Geometry, why are there exactly 27 straight lines on a smooth cubic surface?", Quora. Archived 2026-11-20 at https://perma.cc/38AQ-6ZCM (snapshot of https://suosuo.de/uu0jlKJ). Part II, final Theorem: "If X is smooth, then s_F has transverse zeroes. Therefore X contains exactly 27 lines." First sentence.

import Definitions.Def_cubic_surface_27_layer
import Definitions.Def_cubic_surface_transverse

namespace CubicSurface27

theorem smooth_implies_transverse (F : MvPolynomial (Fin 4) ℂ)
    (hF : IsCubicForm F) (hsm : IsSmoothCubic F) :
    HasTransverseZeroes F := by sorry

end CubicSurface27
