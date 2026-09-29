-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_HomOver_exists_isFrameOn_pullback_of_map_eq_smul
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.exists_isFrameOn_pullback_of_map_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/bf05f7bc-c03f-5fb8-b652-eb24662b7b8e
-- title:
--   Frames and transition function pull back along a `HomOver`
-- statement:
--   Let $\tau\colon R\to S$ be a homomorphism of commutative rings, let $X$ be a scheme with a two-affine open cover $\mathcal V$ (two affine opens $\mathcal V.U_0,\mathcal V.U_1$ with affine intersection whose join is $\top$) and a morphism $c\colon X\to\operatorname{Spec} R$, and likewise let $Y$ carry a two-affine open cover $\mathcal W$ and a morphism $c'\colon Y\to\operatorname{Spec} S$. Let $f$ be a `HomOver` datum for $\tau$, that is, a morphism $f.\mathrm{hom}\colon Y\to X$ with $f.\mathrm{hom}\ ;\ c = c'\ ;\ \operatorname{Spec}(\tau)$ together with the inclusions $\mathcal W.U_i\le f.\mathrm{hom}^{-1}(\mathcal V.U_i)$ for $i=0,1$. Let $M$ be a module on $X$ and let $s_0\in\Gamma(M,\mathcal V.U_0)$, $s_1\in\Gamma(M,\mathcal V.U_1)$ be sections that are frames on their charts, in the sense that for every open $W\le \mathcal V.U_i$ the map $\Gamma(X,W)\to\Gamma(M,W)$, $g\mapsto g\cdot (s_i|_W)$, is bijective. Assume there is $t\in\Gamma(X,\mathcal V.U_0\sqcap \mathcal V.U_1)$ with $s_1|_{\mathcal V.U_0\sqcap\mathcal V.U_1} = t\cdot s_0|_{\mathcal V.U_0\sqcap\mathcal V.U_1}$. Then there exist sections $s_0'\in\Gamma(f^{*}M,\mathcal W.U_0)$ and $s_1'\in\Gamma(f^{*}M,\mathcal W.U_1)$ of the pull-back $f^{*}M=(\mathtt{Scheme.Modules.pullback}\ f.\mathrm{hom}).\mathrm{obj}\ M$ which are frames on $\mathcal W.U_0$ and $\mathcal W.U_1$ respectively, in the same sense, and which satisfy $s_1'|_{\mathcal W.U_0\sqcap\mathcal W.U_1} = (f.\mathrm{map01}\,t)\cdot s_0'|_{\mathcal W.U_0\sqcap\mathcal W.U_1}$, where $f.\mathrm{map01}$ is the $\tau$-semilinear restriction map $\Gamma(X,\mathcal V.U_0\sqcap\mathcal V.U_1)\to\Gamma(Y,\mathcal W.U_0\sqcap\mathcal W.U_1)$ attached to $f$.
--
--   This is the cochain-level functoriality of a two-chart cocycle presentation: a module trivialised on the two charts of $\mathcal V$ by the transition function $t$ pulls back to a module trivialised on the two charts of $\mathcal W$ by $f.\mathrm{map01}\,t$, so that the two-chart Čech class of the presentation is compatible with pull-back. It is used in the relative Picard part of the development, in the comparison of deformation-class maps with the base-change map on two-chart $H^1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_HomOver_exists_isFrameOn_pullback_of_map_eq_smul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.exists_isFrameOn_pullback_of_map_eq_smul
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] {τ : R →+* S}
    {X : Scheme.{u}} {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ Spec (.of R)}
    {Y : Scheme.{u}} {𝒲 : Y.TwoAffineOpenCover} {c' : Y ⟶ Spec (.of S)}
    (f : HomOver τ 𝒱 c 𝒲 c') (M : X.Modules)
    (s₀ : Γ(M, 𝒱.U0)) (s₁ : Γ(M, 𝒱.U1))
    (hs₀ : Scheme.Modules.IsFrameOn s₀ 𝒱.U0) (hs₁ : Scheme.Modules.IsFrameOn s₁ 𝒱.U1)
    (t : Γ(X, 𝒱.U0 ⊓ 𝒱.U1))
    (ht : M.presheaf.map (homOfLE inf_le_right).op s₁ = t • M.presheaf.map (homOfLE inf_le_left).op s₀) :
    ∃ (s₀' : Γ((Scheme.Modules.pullback f.hom).obj M, 𝒲.U0))
      (s₁' : Γ((Scheme.Modules.pullback f.hom).obj M, 𝒲.U1)),
      Scheme.Modules.IsFrameOn s₀' 𝒲.U0 ∧ Scheme.Modules.IsFrameOn s₁' 𝒲.U1 ∧
      ((Scheme.Modules.pullback f.hom).obj M).presheaf.map (homOfLE inf_le_right).op s₁' =
        (show Γ(Y, 𝒲.U0 ⊓ 𝒲.U1) from f.map01 t) •
          ((Scheme.Modules.pullback f.hom).obj M).presheaf.map (homOfLE inf_le_left).op s₀' := by sorry
