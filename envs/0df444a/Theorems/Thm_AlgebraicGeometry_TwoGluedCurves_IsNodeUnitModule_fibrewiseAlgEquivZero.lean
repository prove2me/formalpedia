-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_fibrewiseAlgEquivZero
-- name    : AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.fibrewiseAlgEquivZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/29c5d41d-ce67-56de-a767-315f4f30a100
-- title:
--   Node-unit line bundles are fibrewise algebraically trivial
-- statement:
--   Let $\kappa$ be an algebraically closed field, let $X$ be a reduced scheme with structure morphism $x : X \to \operatorname{Spec}\kappa$, and let $c_1 : C_1 \to \operatorname{Spec}\kappa$, $c_2 : C_2 \to \operatorname{Spec}\kappa$ be $\kappa$-schemes equipped with $\kappa$-morphisms $i_1 : C_1 \to X$, $i_2 : C_2 \to X$ (i.e. $i_1$ followed by $x$ is $c_1$, and likewise for $i_2$) which are closed immersions and whose images together cover the points of $X$. Let $\iota$ be a finite index type and, for each $j$, let $p_1(j)$ be a $\kappa$-point of $C_1$ and $p_2(j)$ a $\kappa$-point of $C_2$, subject to: the closed points underlying the $p_1(j)$ are pairwise distinct; $p_1(j)$ followed by $i_1$ equals $p_2(j)$ followed by $i_2$ for each $j$; any pair of points $q_1 \in C_1$, $q_2 \in C_2$ with the same image in $X$ arises as the pair of closed points of $p_1(j)$, $p_2(j)$ for some $j$; and the fibre product $C_1 \times_X C_2$ (pullback of $i_1$ and $i_2$) is reduced. Let $\varepsilon$ be a $\kappa$-point of $X$, let $h : T \to \operatorname{Spec}\kappa$ be a $\kappa$-scheme, let $u : \iota \to \Gamma(T,\mathcal{O}_T)^\times$, and let $M$ be a rigidified line bundle for $(x,\varepsilon,h)$: an invertible module $M.L$ on $X \times_\kappa T$ (locally isomorphic to the unit sheaf) together with a trivialisation of its pullback along the rigidifying section $\varepsilon \times \mathrm{id}_T$. Assume $M.L$ is a node-unit module for the data $(i_1,i_2,p_1,p_2,h,u)$, that is, there are morphisms $j_1, j_2$ from $M.L$ into the pushforwards along the base-changed immersions $C_1 \times_\kappa T \to X \times_\kappa T$ and $C_2 \times_\kappa T \to X \times_\kappa T$ of the respective unit sheaves such that, over every open $W$ of $X \times_\kappa T$, sections of $M.L$ inject via $m \mapsto (j_1(m), j_2(m))$ and the image consists exactly of the pairs $(f,g)$ whose restrictions to the $j$-th node locus satisfy $f = u(j)\,g$ for all $j$. Then $M$ is fibrewise algebraically equivalent to zero: for every algebraically closed field $k$ and every morphism $s : \operatorname{Spec} k \to T$, the pullback of $M.L$ to the fibre $X_k$ over $s$ admits a scheme $T'$ over $k$, with structure morphism locally of finite type and geometrically integral, an invertible module on $X_k \times_k T'$, and two $k$-points $t_0, t_1$ of $T'$ such that the restriction at $t_0$ is isomorphic to the unit sheaf and the restriction at $t_1$ is isomorphic to that pullback of $M.L$.
--
--   This is the statement that line bundles on two curves glued transversally at finitely many nodes, described by gluing units $u$ along the nodes, lie in the $\operatorname{Pic}^0$ part of the rigidified relative Picard functor, the connecting family being the node-unit family over a split torus of rank $|\iota|$. It is used in the construction of the torus of node units inside the relative Picard functor of a two-glued-curves degeneration and in the identification of its character lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_fibrewiseAlgEquivZero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  AlgebraicGeometry.TwoGluedCurves

theorem AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.fibrewiseAlgEquivZero
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
    (ε : SchemeHomOver (𝟙 (Spec (.of κ))) x)
    {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} {u : ι → Γ(T, ⊤)ˣ} (M : RigidifiedLineBundle x ε h)
    (hu : IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M.L) :
    FibrewiseAlgEquivZero M := by sorry
