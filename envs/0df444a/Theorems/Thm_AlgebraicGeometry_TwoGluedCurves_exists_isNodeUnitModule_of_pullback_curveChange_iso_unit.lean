-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_exists_isNodeUnitModule_of_pullback_curveChange_iso_unit
-- name    : AlgebraicGeometry.TwoGluedCurves.exists_isNodeUnitModule_of_pullback_curveChange_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/43dffa25-09af-52a8-9a56-b3bf1792df64
-- title:
--   Bundles trivial on both components are node-unit modules
-- statement:
--   Let $\kappa$ be an algebraically closed field, let $X$ be a reduced scheme with a morphism $x\colon X\to\operatorname{Spec}\kappa$, and let $c_1\colon C_1\to\operatorname{Spec}\kappa$, $c_2\colon C_2\to\operatorname{Spec}\kappa$ be $\kappa$-schemes equipped with morphisms $i_1\colon C_1\to X$, $i_2\colon C_2\to X$ over $\kappa$ (i.e. $i_k$ followed by $x$ is $c_k$) which are closed immersions, such that every point of $X$ lies in the image of $i_1$ or of $i_2$, and such that the scheme $C_1\times_X C_2$ is reduced. Let $\iota$ be a finite index set and let $p_1(j)\colon\operatorname{Spec}\kappa\to C_1$, $p_2(j)\colon\operatorname{Spec}\kappa\to C_2$ be sections of $c_1$, $c_2$ such that $j\mapsto p_1(j)$ (evaluated at the closed point) is injective, $p_1(j)$ followed by $i_1$ equals $p_2(j)$ followed by $i_2$ for every $j$, and every pair of points $q_1\in C_1$, $q_2\in C_2$ with $i_1(q_1)=i_2(q_2)$ is of the form $(p_1(j),p_2(j))$ for some $j$. Let $h\colon T\to\operatorname{Spec}\kappa$ be a further $\kappa$-scheme and let $L$ be a module on $X\times_{\kappa}T$ which is invertible, in the sense that every point has an open neighbourhood $U$ with the restriction of $L$ to $U$ isomorphic to the unit sheaf of $U$. Assume that the pullbacks of $L$ along the two base-changed immersions $C_k\times_\kappa T\to X\times_\kappa T$ (given by `curveChange`) admit isomorphisms with the unit sheaves of $C_1\times_\kappa T$ and $C_2\times_\kappa T$. Then there is a family of global units $u_j\in\Gamma(T,\mathcal O_T)^\times$, $j\in\iota$, for which $L$ is a node-unit module with gluing units $u$: there are morphisms $j_1, j_2$ from $L$ to the pushforwards of the unit sheaves of $C_1\times_\kappa T$ and $C_2\times_\kappa T$ such that, for every open $W\subseteq X\times_\kappa T$, the map $m\mapsto (j_1(m),j_2(m))$ on sections over $W$ is injective with image exactly the set of pairs $(f,g)$ of functions on the two preimages of $W$ satisfying, for each $j$, the node condition that the restriction of $f$ along the $j$-th section of the first curve equals $u_j$ times the restriction of $g$ along the $j$-th section of the second curve, over the $j$-th node locus in $W$.
--
--   This is the exactness at the middle term of the units–Picard sequence $(\Gamma(T,\mathcal O_T)^\times)^{\iota}\to\operatorname{Pic}(X_T)\to\operatorname{Pic}(C_{1,T})\times\operatorname{Pic}(C_{2,T})$ for a curve obtained by gluing two components transversally at finitely many rational points, in the form needed over an arbitrary base $T$: a line bundle trivial on both base-changed components is described by gluing units along the nodes. It feeds the analysis of the relative Picard functor of two glued smooth curves, in particular the identification of its character lattice and of the torus occurring for the degenerate fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedCurves_exists_isNodeUnitModule_of_pullback_curveChange_iso_unit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra AlgebraicGeometry.TwoGluedCurves

theorem AlgebraicGeometry.TwoGluedCurves.exists_isNodeUnitModule_of_pullback_curveChange_iso_unit
    (κ : Type u) [Field κ] [IsAlgClosed κ]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (.of κ)) [IsReduced X]
    {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x)
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    {ι : Type v} [Finite ι]
    (p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂)
    (hinj : Function.Injective fun j => (p₁ j).1.base (IsLocalRing.closedPoint κ))
    (hnode : ∀ j, (p₁ j).1 ≫ i₁.1 = (p₂ j).1 ≫ i₂.1)
    (hinter : ∀ (q₁ : C₁) (q₂ : C₂), i₁.1.base q₁ = i₂.1.base q₂ →
      ∃ j, q₁ = (p₁ j).1.base (IsLocalRing.closedPoint κ) ∧ q₂ = (p₂ j).1.base (IsLocalRing.closedPoint κ))
    (hcr : IsReduced (pullback i₁.1 i₂.1))
    {T : Scheme.{u}} (h : T ⟶ Spec (.of κ)) (L : (pullback x h).Modules) (hL : Scheme.Modules.IsInvertible L)
    (h₁ : Nonempty ((Scheme.Modules.pullback (curveChange i₁.1 i₁.2 h)).obj L ≅
      SheafOfModules.unit (pullback c₁ h).ringCatSheaf))
    (h₂ : Nonempty ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 h)).obj L ≅
      SheafOfModules.unit (pullback c₂ h).ringCatSheaf)) :
    ∃ u : ι → Γ(T, ⊤)ˣ, IsNodeUnitModule x i₁ i₂ p₁ p₂ h u L := by sorry
