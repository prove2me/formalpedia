-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul
-- name    : AlgebraicGeometry.RelPicard.exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/390d8b76-f7fe-54ed-aa74-b962f9e2e050
-- title:
--   Norm of a 1+ε g cocycle is 1+varepsilonTr(g)
-- statement:
--   Let $R$ be a commutative ring, $c\colon C\to\operatorname{Spec}R$ and $c'\colon C'\to\operatorname{Spec}R$ schemes over it, $A$ a commutative $R$-algebra, and $\mathcal V=(U_0,U_1)$, $\mathcal W=(W_0,W_1)$ two-affine open covers of $C$, $C'$ (two affine opens with affine intersection whose union is everything), pulled back to the base changes $C_A,C_{A[\varepsilon]},C'_A,C'_{A[\varepsilon]}$ along $A$ and the dual numbers $A[\varepsilon]$. Given morphisms $f\colon C'_A\to C_A$ and $f^{\varepsilon}\colon C'_{A[\varepsilon]}\to C_{A[\varepsilon]}$ over the identity of $A$, resp. of $A[\varepsilon]$, carrying the $W_i$ into the preimages of the $U_i$, assume: the square formed by $f^{\varepsilon}$, $f$ and the two thickening maps $C_{A[\varepsilon]}\to C_A$, $C'_{A[\varepsilon]}\to C'_A$ is cartesian; each $W_i$ is exactly the $f$-preimage of $U_i$, and likewise at the $A[\varepsilon]$-level for $f^{\varepsilon}$; $f^{\varepsilon}$ is finite, flat and locally of finite presentation with $\operatorname{finrank}$ equal to a fixed $d$ at every point; and $d$-tuples $e_0,e_1$ of sections of $f^{\varepsilon}_*\mathcal O$ over $U_0^{\varepsilon}$, $U_1^{\varepsilon}$ are given whose restrictions form a $\Gamma(C_{A[\varepsilon]},W)$-basis of $\Gamma(f^{\varepsilon}_*\mathcal O,W)$ for every open $W$ inside the respective chart. Let $L$ be a module on $C'_{A[\varepsilon]}$ with sections $s_0,s_1$ over $W_0^{\varepsilon},W_1^{\varepsilon}$ that are frames there (on every smaller open, multiplication by the restricted section is a bijection from functions to sections), let $g\in\Gamma(C'_A,W_0\cap W_1)$, and assume $s_1=\bigl(1+\varepsilon\cdot\iota(g)\bigr)\,s_0$ on $W_0^{\varepsilon}\cap W_1^{\varepsilon}$, $\iota$ being pull-back along the thickening. Endow $\Gamma(C'_A,W_0\cap W_1)$ with the $\Gamma(C_A,U_0\cap U_1)$-algebra structure given by $f^{*}$ and assume it free and finite as a module. Then there are sections $\Omega_0,\Omega_1$ of $\det_d(f^{\varepsilon}_*L)\otimes\det_d(f^{\varepsilon}_*\mathcal O)^{\vee}$ over $U_0^{\varepsilon},U_1^{\varepsilon}$, each a frame on its chart, with $\Omega_1=\bigl(1+\varepsilon\cdot\iota(\operatorname{Tr}(g))\bigr)\,\Omega_0$ on $U_0^{\varepsilon}\cap U_1^{\varepsilon}$, the trace being taken for the above algebra structure.
--
--   This is the two-chart cocycle form of the statement that the norm (determinant-of-pushforward) construction for line bundles along a finite flat map of constant rank sends the infinitesimal transition function $1+\varepsilon g$ to $1+\varepsilon\operatorname{Tr}(g)$, i.e. that the tangent map of the norm is the trace. It feeds the computation of the action of finite correspondences on first-order deformations of line bundles, and is used in the identification of the germ of the Čech-to-cohomology map with a trace map and in the construction of an isomorphism of the norm module of a dual-number curve change with the unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry NeronModelInfra
  AlgebraicGeometry.RelPicard AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem AlgebraicGeometry.RelPicard.exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul
    {R : Type u} [CommRing R] {C C' : Scheme.{u}} (c : C ⟶ Spec (.of R)) (c' : C' ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover) (𝒲 : C'.TwoAffineOpenCover)
    (f : HomOver (RingHom.id A) (𝒱.pullback c A) (pullback.snd c (specMap R A))
      (𝒲.pullback c' A) (pullback.snd c' (specMap R A)))
    (fε : HomOver (RingHom.id (DualNumber A))
      (𝒱.pullback c (DualNumber A)) (pullback.snd c (specMap R (DualNumber A)))
      (𝒲.pullback c' (DualNumber A)) (pullback.snd c' (specMap R (DualNumber A))))

    (hsq : IsPullback fε.hom (dualNumberThickening A 𝒲 c').hom (dualNumberThickening A 𝒱 c).hom f.hom)

    (hW0 : (𝒲.pullback c' A).U0 = f.hom ⁻¹ᵁ (𝒱.pullback c A).U0)
    (hW1 : (𝒲.pullback c' A).U1 = f.hom ⁻¹ᵁ (𝒱.pullback c A).U1)
    (hW0ε : (𝒲.pullback c' (DualNumber A)).U0 = fε.hom ⁻¹ᵁ (𝒱.pullback c (DualNumber A)).U0)
    (hW1ε : (𝒲.pullback c' (DualNumber A)).U1 = fε.hom ⁻¹ᵁ (𝒱.pullback c (DualNumber A)).U1)

    [IsFinite fε.hom] [Flat fε.hom] [LocallyOfFinitePresentation fε.hom]
    (d : ℕ) (hd : ∀ x, fε.hom.finrank x = d)

    (e₀ : Fin d → Γ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _), (𝒱.pullback c (DualNumber A)).U0))
    (he₀ : ∀ (W : (Limits.pullback c (specMap R (DualNumber A))).Opens) (hW : W ≤ (𝒱.pullback c (DualNumber A)).U0),
      ∃ b : Module.Basis (Fin d) Γ(Limits.pullback c (specMap R (DualNumber A)), W)
          Γ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _), W),
        ∀ i, b i = ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _)).presheaf.map (homOfLE hW).op (e₀ i))
    (e₁ : Fin d → Γ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _), (𝒱.pullback c (DualNumber A)).U1))
    (he₁ : ∀ (W : (Limits.pullback c (specMap R (DualNumber A))).Opens) (hW : W ≤ (𝒱.pullback c (DualNumber A)).U1),
      ∃ b : Module.Basis (Fin d) Γ(Limits.pullback c (specMap R (DualNumber A)), W)
          Γ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _), W),
        ∀ i, b i = ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _)).presheaf.map (homOfLE hW).op (e₁ i))

    (L : (Limits.pullback c' (specMap R (DualNumber A))).Modules)
    (s₀ : Γ(L, (𝒲.pullback c' (DualNumber A)).U0)) (s₁ : Γ(L, (𝒲.pullback c' (DualNumber A)).U1))
    (hs₀ : Scheme.Modules.IsFrameOn s₀ (𝒲.pullback c' (DualNumber A)).U0)
    (hs₁ : Scheme.Modules.IsFrameOn s₁ (𝒲.pullback c' (DualNumber A)).U1)
    (g : ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01)
    (hs : L.presheaf.map (homOfLE inf_le_right).op s₁ =
      (show Γ(Limits.pullback c' (specMap R (DualNumber A)),
          (𝒲.pullback c' (DualNumber A)).U0 ⊓ (𝒲.pullback c' (DualNumber A)).U1)
        from oneAddEpsMul A 𝒲 c' g) • L.presheaf.map (homOfLE inf_le_left).op s₀) :
    letI : Algebra ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01
        ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01 :=
      (f.hom.appLE ((𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1) ((𝒲.pullback c' A).U0 ⊓ (𝒲.pullback c' A).U1)
        f.inf_le).hom.toAlgebra

    ∀ [Module.Free ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01
        ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01]
      [Module.Finite ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01
        ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01],
    ∃ (Ω₀ : Γ(Scheme.Modules.normModule fε.hom d L, (𝒱.pullback c (DualNumber A)).U0))
      (Ω₁ : Γ(Scheme.Modules.normModule fε.hom d L, (𝒱.pullback c (DualNumber A)).U1)),
      Scheme.Modules.IsFrameOn Ω₀ (𝒱.pullback c (DualNumber A)).U0 ∧
      Scheme.Modules.IsFrameOn Ω₁ (𝒱.pullback c (DualNumber A)).U1 ∧
      (Scheme.Modules.normModule fε.hom d L).presheaf.map (homOfLE inf_le_right).op Ω₁ =
        (show Γ(Limits.pullback c (specMap R (DualNumber A)),
            (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1)
          from oneAddEpsMul A 𝒱 c
            (Algebra.trace ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01
              ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01 g)) •
        (Scheme.Modules.normModule fε.hom d L).presheaf.map (homOfLE inf_le_left).op Ω₀ := by sorry
