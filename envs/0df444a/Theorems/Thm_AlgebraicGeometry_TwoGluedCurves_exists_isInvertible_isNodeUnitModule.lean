-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_exists_isInvertible_isNodeUnitModule
-- name    : AlgebraicGeometry.TwoGluedCurves.exists_isInvertible_isNodeUnitModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/3b389d5e-5f4a-59c8-b367-c96fdf062beb
-- title:
--   Invertible node-unit modules with prescribed gluing units exist
-- statement:
--   Let $\kappa$ be an algebraically closed field, let $X$, $C_1$, $C_2$ be schemes, let $x : X \to \operatorname{Spec}\kappa$ with $X$ reduced, and let $c_1 : C_1 \to \operatorname{Spec}\kappa$, $c_2 : C_2 \to \operatorname{Spec}\kappa$ be structure morphisms. Let $i_1$, $i_2$ be morphisms $C_1 \to X$, $C_2 \to X$ over $\operatorname{Spec}\kappa$ (that is, $i_k$ followed by $x$ equals $c_k$), both closed immersions, such that every point of $X$ lies in the image of $i_1$ or of $i_2$. Let $\iota$ be a finite index type and, for each $j$, let $p_1 j$, $p_2 j$ be sections of $c_1$, $c_2$ (i.e. $\kappa$-points of $C_1$, $C_2$), subject to: $j \mapsto (p_1 j)(\text{closed point})$ is injective; $p_1 j$ followed by $i_1$ equals $p_2 j$ followed by $i_2$ for every $j$; and every pair $q_1 \in C_1$, $q_2 \in C_2$ with $i_1(q_1) = i_2(q_2)$ is of the form $(p_1 j)(\text{closed point})$, $(p_2 j)(\text{closed point})$ for some $j$. Assume moreover that the fibre product $C_1 \times_X C_2$ is reduced. Finally let $h : T \to \operatorname{Spec}\kappa$ be a scheme over $\kappa$ and $u : \iota \to \Gamma(T,\mathcal{O}_T)^\times$. Then there exists a sheaf of modules $M$ on $X \times_{\operatorname{Spec}\kappa} T$ which is invertible, in the sense that every point has an open neighbourhood $U$ with $M|_U$ isomorphic to the unit module of $U$, and which is a node-unit module for the data $u$: there are morphisms $j_1 : M \to (i_{1,T})_*\mathcal{O}$, $j_2 : M \to (i_{2,T})_*\mathcal{O}$ to the pushforwards along the base-changed closed immersions of the respective unit modules, such that for every open $W$ of $X \times_{\operatorname{Spec}\kappa} T$ the map $m \mapsto (j_1(m), j_2(m))$ on $\Gamma(M,W)$ is injective with image exactly the set of pairs $(f,g)$ of sections over the two preimages of $W$ satisfying, for every $j$, the node condition that the restriction of $f$ along the $j$-th node section on the first curve equals $u_j$ times the restriction of $g$ along the $j$-th node section on the second curve, over the $j$-th node locus inside $W$.
--
--   This realises the boundary map $(\Gamma(T,\mathcal{O}_T)^\times)^{\iota} \to \operatorname{Pic}(X_T)$ of the units–Picard sequence of a curve glued from two components along finitely many transversal nodes: the gluing units $u$ are turned into an honest line bundle on the base change $X_T$, described as the subsheaf of $(i_{1,T})_*\mathcal{O} \oplus (i_{2,T})_*\mathcal{O}$ cut out by the node conditions. It is used in the construction of the toric part of the relative Picard functor of two glued smooth curves, in particular in the results producing homomorphisms to, and character-lattice descriptions of, that torus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedCurves_exists_isInvertible_isNodeUnitModule.lean

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

theorem AlgebraicGeometry.TwoGluedCurves.exists_isInvertible_isNodeUnitModule
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
    {T : Scheme.{u}} (h : T ⟶ Spec (.of κ)) (u : ι → Γ(T, ⊤)ˣ) :
    ∃ M : (pullback x h).Modules, Scheme.Modules.IsInvertible M ∧
      IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M := by sorry
