-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.dual_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/7a9b09ad-5396-5b75-b017-8e8dcc0a6772
-- title:
--   Invertibility of the dual and L ⊗ L^∨ ≅ 𝒪_X
-- statement:
--   Let $X$ be a scheme and let $L$ be a sheaf of modules on $X$ (an object of `X.Modules`), assumed invertible in the sense of the project predicate `IsInvertible`: for every point $x$ of $X$ there is an open subscheme $U \subseteq X$ with $x \in U$ such that the pullback of $L$ along the open immersion $U \hookrightarrow X$ admits an isomorphism to the unit sheaf of modules on $U$, i.e. to the structure sheaf of $U$ viewed as a module over itself (the isomorphism is only asserted to exist, via `Nonempty`). The conclusion is a conjunction of two assertions. First, the dual `Scheme.Modules.dual L`, defined as the value at the monoidal unit $\mathbb{1}_{X.Modules}$ of the internal hom functor $\mathrm{ihom}\,L$ of the closed monoidal structure on $X$-modules, is again invertible in exactly that local sense. Second, there exists an isomorphism $L \otimes \mathrm{dual}\,L \cong \mathbb{1}_{X.Modules}$ in $X.Modules$, again only asserted as a nonempty type of isomorphisms rather than as a chosen one.
--
--   This is the standard fact that a line bundle on a scheme is invertible for the tensor product with inverse its dual sheaf $\mathcal{H}om_{\mathcal{O}_X}(L, \mathcal{O}_X)$, here in the form adapted to the closed monoidal structure on sheaves of modules, with the inverse given by the named internal-hom dual rather than merely asserted to exist. It underlies the construction of the relative Picard functor and is used throughout the treatment of line bundles, polarisations and rigidified line bundles in this development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.dual_monoidalV2
    {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules}
    (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L) :
    AlgebraicGeometry.Scheme.Modules.IsInvertible (AlgebraicGeometry.Scheme.Modules.dual L) ∧
      Nonempty (L ⊗ AlgebraicGeometry.Scheme.Modules.dual L ≅ 𝟙_ X.Modules) := by sorry
