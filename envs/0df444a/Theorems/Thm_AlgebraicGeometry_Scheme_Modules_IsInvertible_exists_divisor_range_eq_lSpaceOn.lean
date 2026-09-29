-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/f38600eb-d2a2-5fc9-aa41-ba5afa033df4
-- title:
--   Invertible sheaf on a smooth curve is L(D)
-- statement:
--   Let $K$ be a field, $X$ a scheme and $x \colon X \to \operatorname{Spec} K$ a morphism, with $X$ integral and $x$ separated, quasi-compact and smooth of relative dimension $1$; the function field $X.\mathrm{functionField}$ is regarded as a $K$-algebra through the ring map [`AlgebraicCurve.baseToFunctionField x`](def/AlgebraicCurve_CurveModel.html#L18), the structure map on global sections followed by the germ at the generic point. Let $M$ be a sheaf of modules on $X$ which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ for which the pullback of $M$ along $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$. Then there exist a divisor $D$, i.e. a finitely supported function $\mathbb{Z}$-valued on places of $X.\mathrm{functionField}/K$ (a place being a valuation subring containing the image of $K$, distinct from the whole field, and a principal ideal ring), and additive maps $\varphi_U \colon \Gamma(M,U) \to X.\mathrm{functionField}$ indexed by the open sets $U$ of $X$, with the following five properties. First, $\varphi_V(m|_V) = \varphi_U(m)$ whenever $V \le U$ and $V$ is nonempty. Second, $\varphi_U(a \cdot m) = \mathrm{algebraMap}(a)\,\varphi_U(m)$ for $a \in \Gamma(X,U)$ and $U$ nonempty. Third, $\varphi_U$ is injective for $U$ nonempty. Fourth, for every nonempty affine open $U$ the image of $\varphi_U$ is exactly $\{f : v(f) \le \exp(D v) \text{ for all } v \in S_U\}$, where $S_U$ is the set of places whose valuation subring is the image of the stalk of $X$ at some closed point lying in $U$, and $v$ denotes the $\mathbb{Z}^{m0}$-valued adic valuation attached to the maximal ideal of the valuation subring. Fifth, if $s \in \Gamma(M,U)$, $y \in U$ is a closed point of $X$, and every section of $M$ over any open $W \le U$ containing $y$ is a $\Gamma(X,W)$-multiple of $s|_W$, then for every place $v$ whose valuation subring is the image of the stalk at $y$ one has $\exp(D v) = v(\varphi_U(s))$.
--
--   This is the statement that an invertible sheaf on a smooth curve over $K$ is $\mathcal{O}_X(D)$ for a Weil divisor $D$ of the function field, made explicit at the level of sections inside the constant sheaf $K(X)$: the maps $\varphi_U$ send a section to its rational function relative to a trivialisation at the generic point, and $D$ records minus the order of vanishing of the resulting rational section. It feeds the computation of the divisor class group and of the Čech cohomology of line bundles on curve models, for instance the existence of the divisor class map and the recognition of the trivial bundle from its Euler characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated x] [QuasiCompact x] [SmoothOfRelativeDimension 1 x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ (D : AlgebraicCurve.Divisor K X.functionField) (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u)),
      (∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField)) ∧
      (∀ (U : X.Opens) (s : Γ(M, U)) (y : X), y ∈ U → IsClosed ({y} : Set X) →
          (∀ (W : X.Opens) (h : W ≤ U), y ∈ W → ∀ m : Γ(M, W), ∃ a : Γ(X, W), m = a • M.presheaf.map (homOfLE h).op s) →
          ∀ v : AlgebraicCurve.Place K X.functionField,
            (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring →
            WithZero.exp (D v) = v.adicValuation (φ U s)) := by sorry
