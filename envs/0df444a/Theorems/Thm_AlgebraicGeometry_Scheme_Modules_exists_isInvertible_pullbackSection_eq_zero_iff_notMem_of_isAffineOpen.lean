-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullbackSection_eq_zero_iff_notMem_of_isAffineOpen
-- name    : AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullbackSection_eq_zero_iff_notMem_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/f8cb21cf-40a8-544a-8414-6043414dd302
-- title:
--   Affine open complements as zero loci of line bundle sections
-- statement:
--   Let $k$ be a field and let $X$ be a scheme equipped with a morphism $t \colon X \to \operatorname{Spec} k$ which is separated and smooth, the scheme $X$ being integral; let $U$ be an open subset of $X$ which is an affine open (`IsAffineOpen U`). The assertion is that there exist an object $L$ of the category `X.Modules` of sheaves of modules on $X$, a witness that $L$ is invertible in the sense of the project's predicate `Scheme.Modules.IsInvertible`, namely that every point of $X$ has an open neighbourhood $V$ such that the pullback of $L$ along the inclusion $V \hookrightarrow X$ is isomorphic to the unit sheaf of modules `SheafOfModules.unit` of $V$, and a morphism $\theta \colon \mathbb{1} \to L$ from the monoidal unit of `X.Modules`, with the following property: for every field $K$ and every morphism $z \colon \operatorname{Spec} K \to X$, the pulled-back section `pullbackSection z θ` — the inverse of the canonical isomorphism between the pullback of the unit along $z$ and the unit of $\operatorname{Spec} K$, followed by the pullback of $\theta$ — is the zero morphism if and only if the image of the closed point of $\operatorname{Spec} K$ under the base map of $z$ does not lie in $U$.
--
--   This is the statement that on a smooth separated integral $k$-scheme the complement of an affine open subset is the zero locus of a global section of a line bundle, the zero locus being tested on points valued in arbitrary fields; classically it rests on local factoriality of regular local rings together with the fact that the complement of an affine open is of pure codimension one. It is the divisor-theoretic input used in [`AlgebraicGeometry.Scheme.Modules.exists_isInvertible_hom_ne_zero_finite_setOf_stabilizer`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_isInvertible_hom_ne_zero_finite_setOf_stabilizer), on the way to projectivity statements for abelian varieties.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullbackSection_eq_zero_iff_notMem_of_isAffineOpen.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullbackSection_eq_zero_iff_notMem_of_isAffineOpen
    (k : Type u) [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated t] [IsIntegral X] [Smooth t] (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (L : X.Modules) (_ : Scheme.Modules.IsInvertible L) (θ : 𝟙_ X.Modules ⟶ L),
      ∀ (K : Type u) [Field K] (z : Spec (CommRingCat.of K) ⟶ X),
        Scheme.Modules.pullbackSection z θ = 0 ↔ z (IsLocalRing.closedPoint K) ∉ U := by sorry
