-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_eulerChar_pullback_tensor_eq_monoidalV2
-- name    : AlgebraicGeometry.RelPicard.IsAlgEquivZero.eulerChar_pullback_tensor_eq_monoidalV2
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-11T13:23:03.075543+00:00
-- url     : https://prove2.me/theorems/d1fa02bc-4ae5-44be-ab0d-b4ad691450a7
-- title:
--   Algebraic equivalence preserves Euler characteristics on closed subschemes
-- statement:
--   Let $X$ be a proper scheme over a field $k$ and let $L,M$ be invertible sheaves on $X$. Assume that $L$ is algebraically equivalent to the trivial sheaf, witnessed by an invertible sheaf on $X\times_k T$ over a geometrically integral, locally finite-type parameter scheme $T$ with two $k$-rational parameter points giving the trivial sheaf and $L$.
--
--   For every closed immersion $f:Y\hookrightarrow X$,
--
--   $$\chi(Y,f^*(L\otimes M))=\chi(Y,f^*M).$$
--
--   The formal Euler characteristic uses the actual ordered affine Čech complex, and the equality holds for every ordered affine cover of $Y$. There is no dimension restriction and no bound of two charts on that cover. No smoothness, connectedness, or algebraic-closedness assumption on the base field is needed.
--
--   The proof combines local constancy in proper flat families, affine-chart comparisons through the fraction field and residue fields, and functoriality of algebraic equivalence under restriction.
-- source:
--   Stacks Project, Lemma 36.32.2 (Euler characteristics of proper flat families), https://stacks.math.columbia.edu/tag/0B9T. This is the stated consequence for invertible sheaves and algebraic-equivalence families. The proof also adapts Prove2Me submission f9a53e0a-3fc0-5fa5-b07d-98f2b9ba8075 for AlgebraicGeometry.RelPicard.IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq, removing its two-affine-chart restriction.

import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Mathlib.AlgebraicGeometry.Morphisms.Proper

set_option autoImplicit false
open AlgebraicGeometry AlgebraicGeometry.RelPicard CategoryTheory MonoidalCategory
universe u

theorem AlgebraicGeometry.RelPicard.IsAlgEquivZero.eulerChar_pullback_tensor_eq_monoidalV2
    {k : Type u} [Field k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [IsProper a]
    (L M : X.Modules) (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (h0 : IsAlgEquivZero a L) {Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f]
    (U : Y.OrderedAffineCover) :
    (OModulePresheaf.ofModules (f ≫ a) ((Scheme.Modules.pullback f).obj (L ⊗ M))).eulerChar U =
      (OModulePresheaf.ofModules (f ≫ a) ((Scheme.Modules.pullback f).obj M)).eulerChar U := by sorry
