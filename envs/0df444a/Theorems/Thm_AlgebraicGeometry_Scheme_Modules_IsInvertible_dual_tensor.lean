-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.dual_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/1de136b6-0395-5e1e-a8fd-6d35570a9ca9
-- title:
--   Dual of a tensor product of invertible sheaves
-- statement:
--   Let $X$ be a scheme and let $L$ and $M$ be objects of $X.\mathrm{Modules}$, the category of sheaves of modules over the structure sheaf of $X$, equipped with its monoidal (tensor) structure and internal hom. Assume $L$ and $M$ are invertible in the sense of the project predicate [`AlgebraicGeometry.Scheme.Modules.IsInvertible`](def/AlgebraicGeometry_RelativePicardFunctor.html#L16): for every point $x \in X$ there is an open subscheme $U \subseteq X$ with $x \in U$ such that the pullback of the sheaf along the inclusion $U.\iota$ is isomorphic to the unit sheaf of modules on $U$ (the structure sheaf regarded as a module over itself). Writing $\mathrm{dual}\,N = (\mathrm{ihom}\,N).\mathrm{obj}(\mathbf{1})$ for the internal hom from $N$ into the monoidal unit, i.e. $N^{\vee} = \mathcal{H}om_{\mathcal{O}_X}(N,\mathcal{O}_X)$, the conclusion is that the type of isomorphisms $(L \otimes M)^{\vee} \cong L^{\vee} \otimes M^{\vee}$ in $X.\mathrm{Modules}$ is nonempty. Only the existence of such an isomorphism is asserted; no particular isomorphism is named, and no compatibility or naturality is claimed.
--
--   This is the multiplicativity of duality for invertible sheaves, the statement that $L \mapsto L^{\vee}$ inverts the group law on isomorphism classes of line bundles. It is used in the construction of the group structure on the relative Picard functor and in identifying the line bundle of a sum of effective Cartier divisors, and is cited for instance by the results on theta bundles and on inverse ideal sheaf modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.dual_tensor
    {X : AlgebraicGeometry.Scheme.{u}} {L M : X.Modules}
    (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L)
    (hM : AlgebraicGeometry.Scheme.Modules.IsInvertible M) :
    Nonempty (AlgebraicGeometry.Scheme.Modules.dual (L ⊗ M) ≅
      AlgebraicGeometry.Scheme.Modules.dual L ⊗ AlgebraicGeometry.Scheme.Modules.dual M) := by sorry
