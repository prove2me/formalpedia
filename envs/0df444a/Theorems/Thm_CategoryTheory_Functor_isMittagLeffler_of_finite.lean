-- Prove2me | Theorems.Thm_CategoryTheory_Functor_isMittagLeffler_of_finite
-- name    : CategoryTheory.Functor.isMittagLeffler_of_finite
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:15:43.344427+00:00
-- url     : https://prove2.me/theorems/1a5b4178-a11c-41a9-9b23-e19285800c48
-- title:
--   A cofiltered system of finite sets satisfies the Mittag-Leffler condition
-- statement:
--   Let $J$ be a category that is cofiltered or empty, and let $F : J \to \mathbf{Set}$ be a functor such that every $F(j)$ is finite. Then $F$ satisfies the Mittag-Leffler condition: for every object $j$ there is a morphism $f : i \to j$ such that for every morphism $f' : k \to j$,
--   $$\operatorname{im} F(f) \subseteq \operatorname{im} F(f').$$
--
--   The images of the finite sets $F(k)$ in $F(j)$ form a downward-directed family of subsets of a finite set, so they stabilise. The result is used to verify the Mittag-Leffler hypothesis for inverse systems of finite groups, such as cohomology groups with $\mathbb{Z}/\ell^n$ coefficients.
--
--   **Formalization Note** The index category is `J : Type u` with `[Category.{w} J]` and `[IsCofilteredOrEmpty J]`, the functor takes values in `Type v`, and finiteness is `[∀ j, Finite (F.obj j)]`. The conclusion is Mathlib's `Functor.IsMittagLeffler`. The theorem is `CategoryTheory.Functor.isMittagLeffler_of_finite`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/CofilteredSystem.lean, lines 28-31 (`CategoryTheory.Functor.isMittagLeffler_of_finite`).

import Mathlib.CategoryTheory.CofilteredSystem

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe w v u

open Set

namespace CategoryTheory
namespace Functor

theorem isMittagLeffler_of_finite {J : Type u} [Category.{w} J] [IsCofilteredOrEmpty J]
    (F : J ⥤ Type v) [∀ j, Finite (F.obj j)] : F.IsMittagLeffler := by sorry

variable (F : ℕᵒᵖ ⥤ Type v)

end Functor
end CategoryTheory
