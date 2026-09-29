-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigKerDualNumber_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul
-- name    : AlgebraicGeometry.RelPicard.RigKerDualNumber.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/1b6bca25-e619-5f3c-beb5-4cb41e22279b
-- title:
--   Dual-number deformations admit frames with transition 1+ε f
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme, $c\colon C\to\operatorname{Spec}R$ a morphism, and $\varepsilon$ a morphism $\operatorname{Spec}R\to C$ with $\varepsilon$ followed by $c$ equal to the identity, i.e. a section of $c$. Let $A$ be a commutative $R$-algebra and $\mathcal V$ a two-affine open cover of $C$, that is, affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and $U_0\sqcap U_1$ affine. Let $M$ be an element of `RigKerDualNumber.Carrier c ε A`: a rigidified line bundle on $\operatorname{pullback}(c,\operatorname{Spec}R[\,]\to)$ — precisely, an invertible module $M.1.L$ on $C\times_{\operatorname{Spec}R}\operatorname{Spec}A[\epsilon]$ together with a rigidification along the section, subject to the condition that its pullback along the reduction $A[\epsilon]\to A$ is isomorphic, as a module, to the unit module on $C\times_{\operatorname{Spec}R}\operatorname{Spec}A$. Write $U_i^{\epsilon}$ for the preimage of $U_i$ under the first projection of $C\times_{\operatorname{Spec}R}\operatorname{Spec}A[\epsilon]$, and similarly $U_i^{A}$. The assertion is that there are sections $e_0\in\Gamma(M.1.L,U_0^{\epsilon})$, $e_1\in\Gamma(M.1.L,U_1^{\epsilon})$ and an element $f\in\Gamma(C\times_{\operatorname{Spec}R}\operatorname{Spec}A,\;U_0^{A}\sqcap U_1^{A})$ such that $e_0$ is a frame on $U_0^{\epsilon}$ and $e_1$ is a frame on $U_1^{\epsilon}$ — meaning that for every open $W\le U_i^{\epsilon}$ the map $g\mapsto g\cdot(e_i|_W)$ from $\Gamma(X,W)$ to $\Gamma(M.1.L,W)$ is bijective — and, on $U_0^{\epsilon}\sqcap U_1^{\epsilon}$, $e_1|=(1+\epsilon\,\iota f)\cdot e_0|$, where $\iota f$ denotes the image of $f$ under the transition-ring map of the dual-number thickening and $1+\epsilon\,\iota f$ is the section `oneAddEpsMul A 𝒱 c f` of the structure sheaf.
--
--   This is the standard normalisation step in the computation of the kernel of $\operatorname{Pic}(C_{A[\epsilon]})\to\operatorname{Pic}(C_A)$: a line bundle trivial modulo $\epsilon$ is trivialised on each of the two thickened affine charts, and its transition function may be taken of the form $1+\epsilon f$ with $f$ a function on the intersection of the charts over $A$. It feeds the construction of the deformation-class map relating the rigidified relative Picard functor at dual numbers to the two-chart Čech $H^1$ of the structure sheaf.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigKerDualNumber_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard
  AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem AlgebraicGeometry.RelPicard.RigKerDualNumber.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
    (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover) (M : RigKerDualNumber.Carrier c ε A) :
    ∃ (e₀ : Γ(M.1.L, (𝒱.pullback c (DualNumber A)).U0)) (e₁ : Γ(M.1.L, (𝒱.pullback c (DualNumber A)).U1))
      (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01),
      Scheme.Modules.IsFrameOn e₀ (𝒱.pullback c (DualNumber A)).U0 ∧
      Scheme.Modules.IsFrameOn e₁ (𝒱.pullback c (DualNumber A)).U1 ∧
      M.1.L.presheaf.map (homOfLE inf_le_right).op e₁ =
        (show Γ(Limits.pullback c (specMap R (DualNumber A)),
                (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1)
            from oneAddEpsMul A 𝒱 c f) • M.1.L.presheaf.map (homOfLE inf_le_left).op e₀ := by sorry
