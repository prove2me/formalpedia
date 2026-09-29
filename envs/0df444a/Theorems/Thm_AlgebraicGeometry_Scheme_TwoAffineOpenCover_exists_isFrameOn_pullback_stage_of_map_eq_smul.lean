-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isFrameOn_pullback_stage_of_map_eq_smul
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_isFrameOn_pullback_stage_of_map_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/115680a1-fbf7-5706-91e0-41199dc49bcd
-- title:
--   Frames and transition data pull back along stage maps
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme equipped with a two-affine open cover $\mathcal V$ (two opens $U_0,U_1$, each affine, with affine intersection and $U_0\sqcup U_1=\top$), and let $c\colon C\to\operatorname{Spec}R$. Let $\varphi\colon A_0\to A'$ be a morphism of commutative $R$-algebras. Write $C_{A_0}=C\times_{\operatorname{Spec}R}\operatorname{Spec}A_0$, with the induced two-affine cover $\mathcal V$`.pullback`$\,c\,A_0$ whose charts are the preimages of $U_0,U_1$ under the first projection, and similarly for $A'$. Let $M$ be a sheaf of modules on $C_{A_0}$, and let $s_0,s_1$ be sections of $M$ over the two charts which are frames there, in the sense that for every open $W$ contained in the chart, multiplication $g\mapsto g\cdot s_k|_W$ is a bijection from $\Gamma(C_{A_0},W)$ onto $\Gamma(M,W)$. Let $t$ be a section of the structure sheaf of $C_{A_0}$ over the intersection of the two charts with $s_1| = t\cdot s_0|$ there. Then the pullback of $M$ along the stage morphism $C_{A'}\to C_{A_0}$ induced by $\mathrm{id}_C$ and $\operatorname{Spec}\varphi$ admits sections $s_0',s_1'$ over the charts of $\mathcal V$`.pullback`$\,c\,A'$ which are again frames there and satisfy $s_1'| = \mathrm{map01}(t)\cdot s_0'|$ on the intersection, where $\mathrm{map01}$ is the $\varphi$-semilinear map on sections over the intersections induced by the stage morphism.
--
--   This is the chart-packaged functoriality of the two-chart Čech description of an invertible-type module: frames pull back to frames along a base change $A_0\to A'$ of the $R$-algebra, and the transition function is transported by the semilinear map on sections of the structure sheaf. It supports the naturality and surjectivity statements for deformation class maps on relative Picard data, and the dual-numbers computation used there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isFrameOn_pullback_stage_of_map_eq_smul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_isFrameOn_pullback_stage_of_map_eq_smul
    {R : Type u} [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))
    {A₀ A' : Type u} [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] (φ : A₀ →ₐ[R] A')
    (M : (Limits.pullback c (specMap R A₀)).Modules)
    (s₀ : Γ(M, (𝒱.pullback c A₀).U0)) (s₁ : Γ(M, (𝒱.pullback c A₀).U1))
    (hs₀ : Scheme.Modules.IsFrameOn s₀ (𝒱.pullback c A₀).U0)
    (hs₁ : Scheme.Modules.IsFrameOn s₁ (𝒱.pullback c A₀).U1)
    (t : Γ(Limits.pullback c (specMap R A₀), (𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1))
    (ht : M.presheaf.map (homOfLE inf_le_right).op s₁ = t • M.presheaf.map (homOfLE inf_le_left).op s₀) :
    ∃ (s₀' : Γ((Scheme.Modules.pullback (HomOver.stage 𝒱 c φ).hom).obj M, (𝒱.pullback c A').U0))
      (s₁' : Γ((Scheme.Modules.pullback (HomOver.stage 𝒱 c φ).hom).obj M, (𝒱.pullback c A').U1)),
      Scheme.Modules.IsFrameOn s₀' (𝒱.pullback c A').U0 ∧ Scheme.Modules.IsFrameOn s₁' (𝒱.pullback c A').U1 ∧
      ((Scheme.Modules.pullback (HomOver.stage 𝒱 c φ).hom).obj M).presheaf.map (homOfLE inf_le_right).op s₁' =
        (show Γ(Limits.pullback c (specMap R A'), (𝒱.pullback c A').U0 ⊓ (𝒱.pullback c A').U1) from
          (HomOver.stage 𝒱 c φ).map01 t) •
        ((Scheme.Modules.pullback (HomOver.stage 𝒱 c φ).hom).obj M).presheaf.map (homOfLE inf_le_left).op s₀' := by sorry
