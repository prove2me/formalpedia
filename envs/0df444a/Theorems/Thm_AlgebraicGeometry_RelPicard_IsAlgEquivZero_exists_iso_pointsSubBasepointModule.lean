-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_exists_iso_pointsSubBasepointModule
-- name    : AlgebraicGeometry.RelPicard.IsAlgEquivZero.exists_iso_pointsSubBasepointModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/a59358c5-49f5-51f8-8ff7-1cf47628ea17
-- title:
--   Line bundle algebraically equivalent to zero is 𝒪(sum Pᵢ-dε)
-- statement:
--   Let $k$ be an algebraically closed field and let $a : A \to \operatorname{Spec} k$ be a morphism of schemes that is proper, smooth of relative dimension one and geometrically integral. Let $\varepsilon$ be a $k$-point of $A$, that is, a morphism $\operatorname{Spec} k \to A$ composing with $a$ to the identity, and assume that for every $m_0 \in \mathbb{N}$ there is a datum `SmoothProperCurve.FiniteMapData a ε` with invariant $m \ge m_0$: a cover of $A$ by two affine opens $U$, $V$ with $U$ the complement of the image of $\varepsilon$, sections $f \in \Gamma(A,U)$, $g \in \Gamma(A,V)$ whose basic opens both equal $U \cap V$ and whose restrictions there multiply to $1$, making $\Gamma(A,U)$ and $\Gamma(A,V)$ finite over $k[X]$, and with every fibre $S \otimes_k \Gamma(A,U)/(1\otimes f - s\otimes 1)$ finite free of rank $m$ over any local $k$-algebra $S$ and $s \in S$. Let $L$ be a module on $A$ that is invertible, i.e. locally isomorphic to the structure sheaf, and suppose $L$ is algebraically equivalent to zero in the sense of `IsAlgEquivZero`: there are a scheme $T'$ over $k$ that is locally of finite type and geometrically integral, an invertible module $M$ on $A \times_k T'$ and $k$-points $t_0, t_1$ of $T'$ such that the pullback of $M$ along the base change of $t_0$ is isomorphic to the unit module on $A \times_{\operatorname{Spec} k} \operatorname{Spec} k$ (the pullback of $a$ along the identity) and the pullback along $t_1$ is isomorphic to the pullback of $L$ along the first projection. The conclusion asserts the existence of a finite list $P_1,\dots,P_d$ of $k$-points of $A$ together with an isomorphism between the pullback of $L$ along the first projection and the iterated tensor product $\bigotimes_{i=1}^d \bigl(\mathcal{O}(P_i) \otimes \mathfrak{I}_\varepsilon\bigr)$, where $\mathcal{O}(P_i)$ is the line bundle of the relative effective Cartier divisor cut out by $P_i$ and $\mathfrak{I}_\varepsilon$ the ideal module of the divisor cut out by $\varepsilon$, the empty list giving the unit module; the isomorphism is asserted as non-emptiness of the type of isomorphisms.
--
--   This is the surjectivity of the Abel–Jacobi map on $k$-points for a smooth proper curve with a rational base point: every line bundle of degree zero, here in the form of algebraic equivalence to zero, is of the shape $\mathcal{O}(P_1+\cdots+P_d-d\varepsilon)$. It is the converse direction to the statement that such bundles are algebraically equivalent to zero, and it is used in the construction of the theta bundle for families of line bundles that are fibrewise algebraically equivalent to zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_exists_iso_pointsSubBasepointModule.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.IsAlgEquivZero.exists_iso_pointsSubBasepointModule
    {k : Type u} [Field k] [IsAlgClosed k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsProper a] [SmoothOfRelativeDimension 1 a] [GeometricallyIntegral a]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData a ε, m₀ ≤ 𝔉.m) {L : A.Modules}
    (hL : Scheme.Modules.IsInvertible L) (h0 : IsAlgEquivZero a L) :
    ∃ Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a),
      Nonempty ((Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj L ≅ pointsSubBasepointModule (a := a) ε Ps) := by sorry
