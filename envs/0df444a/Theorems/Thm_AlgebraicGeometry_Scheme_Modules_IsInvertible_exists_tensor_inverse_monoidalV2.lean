-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensor_inverse_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/67d0462b-0f64-5445-ad67-d68ecedc992a
-- title:
--   Invertible modules on a scheme admit tensor inverses
-- statement:
--   Let $X$ be a scheme (in a fixed universe $u$) and let $L$ be an object of the category $X.Modules$ of sheaves of modules over the sheaf of rings of $X$. Assume $L$ satisfies the project's invertibility predicate [`AlgebraicGeometry.Scheme.Modules.IsInvertible`](def/AlgebraicGeometry_RelativePicardFunctor.html#L16), which by definition asserts local triviality in the following sense: for every point $x$ of $X$ there is an open subset $U \subseteq X$ with $x \in U$ such that the type of isomorphisms between the pullback of $L$ along the open immersion $U.\iota \colon U \to X$ and the unit module $\mathcal{O}_U$ (the structure sheaf of $U$ viewed as a module over itself) is nonempty. The conclusion is that there exists an object $M$ of $X.Modules$ which is again invertible in the same sense, together with a nonempty type of isomorphisms $L \otimes M \cong \mathbb{1}$, where $\otimes$ and $\mathbb{1}$ are the tensor product and unit of the monoidal structure on $X.Modules$ (the unit being the structure sheaf of $X$ as a module over itself). Only the bare existence of such an isomorphism is asserted, via `Nonempty`; no chosen isomorphism, and no naturality or coherence statement, is part of the conclusion.
--
--   This is the statement that every line bundle on a scheme has an inverse for the tensor product, so that isomorphism classes of invertible modules form a group rather than only a monoid; the inverse is the dual $\mathcal{H}om_{\mathcal{O}_X}(L, \mathcal{O}_X)$. It underlies the construction of the relative Picard functor used in the treatment of polarisations and of Euler characteristics of tensor products of line bundles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse_monoidalV2.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensor_inverse_monoidalV2
    {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules}
    (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L) :
    ∃ M : X.Modules, AlgebraicGeometry.Scheme.Modules.IsInvertible M ∧
      Nonempty (L ⊗ M ≅ 𝟙_ X.Modules) := by sorry
