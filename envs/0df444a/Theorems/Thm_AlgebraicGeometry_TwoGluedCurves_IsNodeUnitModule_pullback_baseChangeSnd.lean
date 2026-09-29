-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_pullback_baseChangeSnd
-- name    : AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.pullback_baseChangeSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/873f74f2-1e35-5cfe-b478-eba36df281a0
-- title:
--   Node-unit modules are stable under base change in T
-- statement:
--   Let $\kappa$ be an algebraically closed field, let $x\colon X\to\operatorname{Spec}\kappa$ be a reduced $\kappa$-scheme, and let $c_1\colon C_1\to\operatorname{Spec}\kappa$, $c_2\colon C_2\to\operatorname{Spec}\kappa$ be $\kappa$-schemes equipped with morphisms $i_1,i_2$ to $X$ over $\kappa$ (elements of `SchemeHomOver`, i.e. morphisms whose composite with $x$ is $c_1$, resp. $c_2$) which are closed immersions and whose images cover the points of $X$. Let $\iota$ be a finite index type and, for each $j$, let $p_1 j$, $p_2 j$ be sections of $c_1$, $c_2$ over $\operatorname{Spec}\kappa$, subject to: the points $(p_1 j)(\text{closed point})$ of $C_1$ are pairwise distinct; $p_1 j$ followed by $i_1$ equals $p_2 j$ followed by $i_2$ for every $j$; every pair $(q_1,q_2)\in C_1\times C_2$ with $i_1(q_1)=i_2(q_2)$ is of the form $((p_1 j)(\text{closed point}),(p_2 j)(\text{closed point}))$; and $C_1\times_X C_2$ is reduced. Let $h\colon T\to\operatorname{Spec}\kappa$, let $u\colon\iota\to\Gamma(T,\mathcal O_T)^\times$, and let $M$ be a sheaf of modules on $X\times_\kappa T$ which is invertible (every point has a neighbourhood $U$ on which the restriction of $M$ along $U\hookrightarrow X\times_\kappa T$ is isomorphic to the structure sheaf) and satisfies `IsNodeUnitModule` for the data $(x,i_1,i_2,p_1,p_2,h,u)$: there are morphisms $j_1\colon M\to (i_{1,T})_*\mathcal O_{C_1\times_\kappa T}$ and $j_2\colon M\to (i_{2,T})_*\mathcal O_{C_2\times_\kappa T}$, along the base-changed immersions, such that for every open $W\subseteq X\times_\kappa T$ the map $m\mapsto (j_1(m),j_2(m))$ on $\Gamma(M,W)$ is injective with image exactly the pairs $(f,g)$ satisfying, for every $j$, the node condition that the restriction of $f$ along the $j$-th section of the first curve equals $u_j$ times the restriction of $g$ along the $j$-th section of the second curve, both restricted to the $j$-th node locus in $W$. Then for any $h'\colon T'\to\operatorname{Spec}\kappa$ and any morphism $\psi\colon T'\to T$ over $\kappa$, the pullback of $M$ along $\mathrm{id}_X\times\psi\colon X\times_\kappa T'\to X\times_\kappa T$ again satisfies `IsNodeUnitModule` for the same geometric data over $T'$, with gluing units the images $\psi^\ast(u_j)\in\Gamma(T',\mathcal O_{T'})^\times$ under the map on global sections induced by $\psi$.
--
--   This is the naturality in the parameter scheme $T$ of the construction attaching to a family of units $(u_j)\in(\Gamma(T,\mathcal O_T)^\times)^{\iota}$ the line bundle on $X\times_\kappa T$ obtained by gluing the structure sheaves of the two base-changed curves at the $\iota$ nodes. It is used in the identification of the relative Picard functor of a curve with two transversally crossing components as a torus with explicit character lattice, and in the attendant compatibility statements for the kernel of the restriction map to the two components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_pullback_baseChangeSnd.lean

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

theorem AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.pullback_baseChangeSnd
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
    {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} {u : ι → Γ(T, ⊤)ˣ} {M : (pullback x h).Modules}
    (hM : Scheme.Modules.IsInvertible M) (hu : IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M)
    {T' : Scheme.{u}} {h' : T' ⟶ Spec (.of κ)} (ψ : SchemeHomOver h' h) :
    IsNodeUnitModule x i₁ i₂ p₁ p₂ h' (fun j => Units.map ψ.1.appTop.hom.toMonoidHom (u j))
      ((Scheme.Modules.pullback (baseChangeSnd x ψ)).obj M) := by sorry
