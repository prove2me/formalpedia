-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_forall_invertible_free
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_forall_invertible_free
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/d6498db0-d114-5af5-b34e-a4cb37364a95
-- title:
--   Invertible modules on Spec R are trivial when Pic R vanishes
-- statement:
--   Let $R$ be a commutative ring (in a fixed universe) with the property that every $R$-module $N$ which is invertible in the sense of `Module.Invertible` is free. Let $X = \operatorname{Spec}(R)$ and let $L$ be an object of the category $X$`.Modules` of sheaves of modules over the structure sheaf of $X$, and suppose $L$ satisfies `Scheme.Modules.IsInvertible`, i.e. the single field of that structure: for every point $x$ of $X$ there is an open subset $U \subseteq X$ with $x \in U$ such that the pullback of $L$ along the inclusion $U \hookrightarrow X$ admits an isomorphism to the unit sheaf of modules $\mathcal{O}_U$ on $U$ (the isomorphism is asserted only as a nonempty type, no compatibility between the local trivialisations being required). The conclusion is that the type of isomorphisms from $L$ to the monoidal unit $\mathbb{1}$ of $X$`.Modules` is nonempty; that is, $L \cong \mathcal{O}_X$ globally, the isomorphism being produced without any canonical choice being claimed.
--
--   This is the affine case of the identification of the Picard group of $\operatorname{Spec} R$ with the Picard group of $R$: a locally trivial sheaf of modules on an affine scheme over a ring with trivial Picard group is globally trivial. It is used in the construction of sections trivialising powers of invertible modules on smooth proper curves, where the hypothesis that every invertible $R$-module is free is consumed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_forall_invertible_free.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_forall_invertible_free
    (R : Type u) [CommRing R]
    (hPic : ∀ (N : Type u) [AddCommGroup N] [Module R N], Module.Invertible R N → Module.Free R N)
    (L : (Spec (CommRingCat.of R)).Modules) (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (L ≅ 𝟙_ (Spec (CommRingCat.of R)).Modules) := by sorry
