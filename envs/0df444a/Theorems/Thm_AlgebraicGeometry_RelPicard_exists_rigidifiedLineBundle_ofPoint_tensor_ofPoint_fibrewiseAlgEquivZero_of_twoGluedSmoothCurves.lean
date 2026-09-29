-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_rigidifiedLineBundle_ofPoint_tensor_ofPoint_fibrewiseAlgEquivZero_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.exists_rigidifiedLineBundle_ofPoint_tensor_ofPoint_fibrewiseAlgEquivZero_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/3eadc8c7-f29d-59cd-bdd6-05902f7b9100
-- title:
--   Rigidified 𝒪_X(P)⊗𝒪_X(-Q) on a two-component curve is fibrewise algebraically trivial
-- statement:
--   Let $k$ be an algebraically closed field, let $x : X \to \operatorname{Spec} k$ be proper with $X$ reduced, and let $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1, i_2$ be morphisms $C_1 \to X$, $C_2 \to X$ over $\operatorname{Spec} k$ (that is, $i_j$ followed by $x$ equals $c_j$) which are closed immersions and are jointly surjective on points, assume the scheme-theoretic intersection $C_1 \times_X C_2$ is reduced, and let $s$ be a natural number with $0 < s$ equal to the number of points of that intersection. Let $\varepsilon$ be a section of $x$ (a morphism $\operatorname{Spec} k \to X$ with $\varepsilon$ followed by $x$ the identity), and let $P, Q$ be sections of $c_1$ whose images in $X$, namely the images of the closed point of $\operatorname{Spec} k$ under $P$ followed by $i_1$ and under $Q$ followed by $i_1$, avoid the image of $i_2$. Then there is a rigidified line bundle $M$ for $(x, \varepsilon)$ over the base $\operatorname{Spec} k$ with the identity structure morphism, that is, an $\mathcal{O}$-module $M.L$ on $X \times_{\operatorname{Spec} k} \operatorname{Spec} k$ that is locally isomorphic to the unit module and whose pullback along the section determined by $\varepsilon$ is isomorphic to the unit module, such that $M.L$ is isomorphic to the tensor product of the dual ideal module of the degree-one relative effective Cartier divisor attached to the graph of $P$ followed by $i_1$ with the ideal module of the divisor attached to the graph of $Q$ followed by $i_1$, and such that $M$ satisfies `FibrewiseAlgEquivZero`: for every algebraically closed field $K$ and every morphism $\operatorname{Spec} K \to \operatorname{Spec} k$, the pullback of $M.L$ to the corresponding fibre is algebraically equivalent to zero in the sense that it is joined to the unit module by an invertible module over the base change along a locally of finite type, geometrically integral parameter scheme, evaluated at two $K$-points of that parameter.
--
--   This is the Abel–Jacobi statement that, on a reduced proper curve glued from two smooth geometrically integral curves meeting in finitely many points, the divisor class $[P]-[Q]$ supported on the smooth locus of one component gives a rigidified line bundle lying in the degree-zero (algebraically trivial) part of the relative Picard functor. It feeds the Raynaud-style dictionary for the Picard functor of such glued curves and is used in the analysis of models of the modular curves $X_1(p)$ and $X_H$ to identify the bundle attached to a prescribed divisor class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_rigidifiedLineBundle_ofPoint_tensor_ofPoint_fibrewiseAlgEquivZero_of_twoGluedSmoothCurves.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.exists_rigidifiedLineBundle_ofPoint_tensor_ofPoint_fibrewiseAlgEquivZero_of_twoGluedSmoothCurves
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (ε : SchemeHomOver (𝟙 _) x)
    (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁)
    (hP : (P.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base)
    (hQ : (Q.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base) :
    ∃ M : RigidifiedLineBundle x ε (𝟙 (Spec (CommRingCat.of k))),
      Nonempty (M.L ≅
        (RelEffCartierDiv.ofPoint x (P.1 ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact P.2)).lineBundle ⊗
          (RelEffCartierDiv.ofPoint x (Q.1 ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact Q.2)).idealModule) ∧
      FibrewiseAlgEquivZero M := by sorry
