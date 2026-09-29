-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_isNodeUnitModule_one_unit
-- name    : AlgebraicGeometry.TwoGluedCurves.isNodeUnitModule_one_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/56a96cba-7e5c-5e1e-aa5b-a8b274bca10f
-- title:
--   Unit module is a node-unit module with gluing units 1
-- statement:
--   Let $\kappa$ be an algebraically closed field, let $X$, $C_1$, $C_2$ be schemes, let $x\colon X\to\operatorname{Spec}\kappa$ with $X$ reduced, and let $c_1\colon C_1\to\operatorname{Spec}\kappa$, $c_2\colon C_2\to\operatorname{Spec}\kappa$ be given. Let $i_1$, $i_2$ be morphisms $C_1\to X$, $C_2\to X$ over $\operatorname{Spec}\kappa$ (i.e. $i_k$ followed by $x$ equals $c_k$) whose underlying scheme morphisms are closed immersions, such that every point of $X$ lies in the image of $i_1$ or of $i_2$, and such that the fibre product $C_1\times_X C_2$ is reduced. Let $\iota$ be a finite index type and, for $j\in\iota$, let $p_1(j)\colon\operatorname{Spec}\kappa\to C_1$ and $p_2(j)\colon\operatorname{Spec}\kappa\to C_2$ be sections of $c_1$, $c_2$ respectively, with $j\mapsto p_1(j)(\text{closed point})$ injective, with $p_1(j)$ followed by $i_1$ equal to $p_2(j)$ followed by $i_2$ for all $j$, and such that every pair $(q_1,q_2)\in C_1\times C_2$ with $i_1(q_1)=i_2(q_2)$ is of the form $(p_1(j)(\text{closed point}),p_2(j)(\text{closed point}))$ for some $j$. Finally let $h\colon T\to\operatorname{Spec}\kappa$ be arbitrary. The conclusion is that the structure sheaf $\mathcal O_{X_T}$ of $X_T=X\times_{\operatorname{Spec}\kappa}T$ satisfies `IsNodeUnitModule` for the constant family of gluing units $1$: there are morphisms of modules $j_1\colon\mathcal O_{X_T}\to (i_{1,T})_*\mathcal O_{C_{1,T}}$ and $j_2\colon\mathcal O_{X_T}\to (i_{2,T})_*\mathcal O_{C_{2,T}}$, where $i_{k,T}$ denotes the base change `curveChange` of $i_k$ along $h$, such that for every open $W\subseteq X_T$ the map $m\mapsto (j_1(m),j_2(m))$ on sections over $W$ is injective with image exactly the set of pairs $(f,g)$ of sections over the two preimages of $W$ whose restrictions along the $j$-th node sections of $C_{1,T}$ and $C_{2,T}$ agree on the $j$-th node locus in $W$, for every $j\in\iota$ (the unit factor being $1$).
--
--   This is the Mayer–Vietoris (conductor) description of the structure sheaf of a reduced scheme written as the union of two closed subschemes crossing transversally at rational points, stated after an arbitrary base change $T\to\operatorname{Spec}\kappa$ and phrased as the assertion that $\mathcal O_{X_T}$ is the node-unit module attached to the trivial family of gluing units. It serves as the existence statement for node-unit modules, and is used in the analysis of the relative Picard functor of two glued smooth curves, in particular in the construction of rigidified line bundles and of the character lattice of the associated torus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedCurves_isNodeUnitModule_one_unit.lean

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

theorem AlgebraicGeometry.TwoGluedCurves.isNodeUnitModule_one_unit
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
    {T : Scheme.{u}} (h : T ⟶ Spec (.of κ)) :
    IsNodeUnitModule x i₁ i₂ p₁ p₂ h 1 (SheafOfModules.unit (pullback x h).ringCatSheaf) := by sorry
