-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_pow_maximalIdeal_smul_cech_sliceAt_stalk_eq_bot
-- name    : AlgebraicGeometry.Polarisation.exists_pow_maximalIdeal_smul_cech_sliceAt_stalk_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/5a0764b6-d932-51ee-8ec6-b99c4448beb0
-- title:
--   A power of mathfrak m_y kills the sliced Čech cohomology
-- statement:
--   Let $K$ be an algebraically closed field, $f : A \to \operatorname{Spec} K$ a morphism of schemes, $L$ a relative group law on $f$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} K$, natural in $T$), assumed commutative, and let `AbelianSchemePropertyBundle K f` hold: $f$ is smooth and proper, every fibre of $f$ is connected, and a relative group law exists. Assume $f$ is smooth of relative dimension $g$. Let $M$ be an $\mathcal O_A$-module that is invertible, in the sense that every point has an open neighbourhood $U$ over which the restriction of $M$ is isomorphic to the unit module. Let $\kappa : KM \to A$ be a closed immersion with $\kappa$ followed by $f$ finite, and assume that for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} K$ and every point $x$ of $A$ over $t$, the point $x$ factors through $\kappa$ if and only if $x$ lies in the stabiliser of $M$, i.e. the pullback of $M$ along translation by $x$ is locally isomorphic, over the projection $\operatorname{pr}_2 : A \times_K \operatorname{Spec} R \to \operatorname{Spec} R$, to the pullback of $M$ along $\operatorname{pr}_1$. Let $N$ be a second invertible $\mathcal O_A$-module, and let $\mathcal K$ be an ordered affine cover of $A$ (a finite linearly ordered family of affine opens covering $A$) with exactly $g+1$ members. Fix a point $y \in A$ and put $R := \mathcal O_{A,y}$, let $b_R : \operatorname{Spec} R \to A$ be the canonical morphism from the stalk, $t_R := b_R$ followed by $f$, and $x_R := (b_R, \mathrm{rfl})$ the corresponding point of $A$ over $t_R$. Let $F_R$ be the pullback, along the slice morphism $A \times_K \operatorname{Spec} R \to A \times_K A$ with components $\operatorname{pr}_1$ and $b_R \circ \operatorname{pr}_2$, of the Mumford bundle $m^*M \otimes (\operatorname{pr}_1^* M^{\vee} \otimes \operatorname{pr}_2^* M^{\vee})$ tensored with $\operatorname{pr}_2^* N$; let $\mathcal K_R$ be the ordered affine cover of $A \times_K \operatorname{Spec} R$ obtained by taking preimages of the members of $\mathcal K$ under $\operatorname{pr}_1$, and let $G$ be the $\mathcal O$-module presheaf $U \mapsto \Gamma(F_R, U)$ with its $R$-module structure coming from the structure morphism $A \times_K \operatorname{Spec} R \to \operatorname{Spec} R$. Then there is a single $n \in \mathbb N$ such that $\mathfrak m_R^{\,n}$ annihilates the whole of the Čech module $G.H0\ \mathcal K_R$ and, for every $i$, the whole of $G.HSucc\ \mathcal K_R\ i$, the quotient of $\ker d_{i+1}$ by the image of $d_i$.
--
--   This is the finite-support statement for the Čech cohomology of the Mumford bundle $\Lambda(M) \otimes \operatorname{pr}_2^* N$ restricted to the slice over $\operatorname{Spec}\mathcal O_{A,y}$: all cohomology in all degrees is killed by one power of the maximal ideal, so each Čech module is of finite length over the local ring. It feeds the computation of the Euler characteristic of $\Lambda(M) \otimes \operatorname{pr}_2^* N$ as $(-1)^{\dim}$ times the rank of the stabiliser scheme, the degree-theoretic input to the Riemann–Roch style count on the abelian scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_pow_maximalIdeal_smul_cech_sliceAt_stalk_eq_bot.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_pow_maximalIdeal_smul_cech_sliceAt_stalk_eq_bot
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    {KM : Scheme.{0}} (κ : KM ⟶ A) (hκ : IsClosedImmersion κ) (hfin : IsFinite (κ ≫ f))
    (hK : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      (∃ x₀ : Spec (CommRingCat.of R) ⟶ KM, x₀ ≫ κ = x.1) ↔ L.IsInStabilizer M t x)
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝒦 : A.OrderedAffineCover) (h𝒦 : Fintype.card 𝒦.ι = g + 1) (y : A) :
    letI R : Type := ↥(A.presheaf.stalk y)
    letI bR : Spec (CommRingCat.of R) ⟶ A := A.fromSpecStalk y
    letI tR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K) := bR ≫ f
    letI xR : SchemeHomOver tR f := ⟨bR, rfl⟩
    letI FR : (pullback f tR).Modules :=
      (Scheme.Modules.pullback (sliceAt f xR)).obj
        (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N)
    letI _ : IsAffineHom (pullback.fst f tR) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒦R : (pullback f tR).OrderedAffineCover := 𝒦.comap (pullback.fst f tR)
    letI G := OModulePresheaf.ofModules (pullback.snd f tR) FR
    ∃ n : ℕ, IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R (G.H0 𝒦R)) = ⊥ ∧
      ∀ i : ℕ, IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R (G.HSucc 𝒦R i)) = ⊥ := by sorry
