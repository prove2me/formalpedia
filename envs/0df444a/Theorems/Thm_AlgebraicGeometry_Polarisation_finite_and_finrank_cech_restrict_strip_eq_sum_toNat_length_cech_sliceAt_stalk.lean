-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_finite_and_finrank_cech_restrict_strip_eq_sum_toNat_length_cech_sliceAt_stalk
-- name    : AlgebraicGeometry.Polarisation.finite_and_finrank_cech_restrict_strip_eq_sum_toNat_length_cech_sliceAt_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/1fbde8f3-fb1a-571a-ae1a-6bdd05658050
-- title:
--   Čech cohomology on an affine strip as a sum of stalk lengths
-- statement:
--   Let $K$ be an algebraically closed field, $f : A \to \operatorname{Spec} K$ a morphism of schemes, $L$ a relative group law on $f$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} K$) which is commutative, and assume the bundle `AbelianSchemePropertyBundle K f`, i.e. $f$ is smooth and proper with connected fibres and admits a relative group law. Let $M$ be an invertible $\mathcal O_A$-module (locally isomorphic to the unit), let $\kappa : KM \to A$ be a closed immersion with $\kappa$ followed by $f$ finite, and assume that for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} K$ and every $R$-point $x$ of $A$ over $t$, the point $x$ factors through $\kappa$ precisely when $x$ lies in the stabiliser of $M$, in the sense that the pullback of $M$ along right translation by $x$ and the pullback of $M$ along the first projection are locally isomorphic over $\operatorname{Spec} R$ via $\mathrm{pr}_2$. Let $N$ be a further invertible $\mathcal O_A$-module, $\mathcal K$ a finite ordered affine open cover of $A$, $V \subseteq A$ an affine open, $W$ an open of $A \times_K A$ with $W = \mathrm{pr}_2^{-1}(V)$, $\mathfrak W$ any finite ordered affine open cover of the scheme $W$, and $T_V$ a finite set of points of $KM$ consisting exactly of those $y'$ with $\kappa(y') \in V$. Put $F = \Lambda(M) \otimes \mathrm{pr}_2^{*} N$ on $A \times_K A$, where $\Lambda(M)$ is the Mumford bundle $m^{*}M \otimes (\mathrm{pr}_1^{*}M^{\vee} \otimes \mathrm{pr}_2^{*}M^{\vee})$ for the addition morphism $m$ attached to $L$, and let $GW$ be the presheaf of modules of sections of $F$ restricted to $W$, viewed over $K$ through $W \hookrightarrow A \times_K A$ followed by $\mathrm{pr}_1$ and $f$. Then the degree-zero Čech cohomology $H^0(\mathfrak W, GW)$ is a finite-dimensional $K$-vector space, and its dimension equals $\sum_{y' \in T_V} \operatorname{length}_{R}$ of the degree-zero Čech cohomology, for the cover $\mathcal K$ pulled back along $\mathrm{pr}_1$, of the slice of $F$ along $\operatorname{Spec} R \to A$ regarded over $R$ through $\mathrm{pr}_2$, where $R = \mathcal O_{A, \kappa(y')}$ and the lengths are read as natural numbers via `ENat.toNat`; and the same two assertions hold for every $H^{i+1}$, the cohomology $\ker d^{i+1} / \operatorname{im} d^{i}$ of the Čech complexes.
--
--   This is the single-strip, degree-by-degree form of the comparison between the cohomology of the twisted Mumford bundle on a strip $A \times V$ of $A \times_K A$ and the cohomology of its slices at the points of the stabiliser lying in $V$, computed after localisation at the stalks. It is the ingredient from which the Euler-characteristic identity [`AlgebraicGeometry.Polarisation.eulerChar_mumfordBundle_tensor_pullback_snd_eq_sum_alternating_length_of_forall_mem`](thm.html#AlgebraicGeometry.Polarisation.eulerChar_mumfordBundle_tensor_pullback_snd_eq_sum_alternating_length_of_forall_mem) is assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_finite_and_finrank_cech_restrict_strip_eq_sum_toNat_length_cech_sliceAt_stalk.lean

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

theorem AlgebraicGeometry.Polarisation.finite_and_finrank_cech_restrict_strip_eq_sum_toNat_length_cech_sliceAt_stalk
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    {KM : Scheme.{0}} (κ : KM ⟶ A) (hκ : IsClosedImmersion κ) (hfin : IsFinite (κ ≫ f))
    (hK : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      (∃ x₀ : Spec (CommRingCat.of R) ⟶ KM, x₀ ≫ κ = x.1) ↔ L.IsInStabilizer M t x)
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝒦 : A.OrderedAffineCover)
    (V : A.Opens) (hV : IsAffineOpen V)
    (W : (pullback f f).Opens) (hW : W = (pullback.snd f f) ⁻¹ᵁ V)
    (𝔚 : (W : Scheme.{0}).OrderedAffineCover)
    (TV : Finset KM) (hTV : ∀ y' : KM, y' ∈ TV ↔ κ.base y' ∈ V) :
    letI F : (pullback f f).Modules := mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N
    letI GW := OModulePresheaf.ofModules (W.ι ≫ pullback.fst f f ≫ f) (F.restrict W.ι)
    (Module.Finite K (GW.H0 𝔚) ∧
      Module.finrank K (GW.H0 𝔚) =
        ∑ y' ∈ TV,
          letI y : A := κ.base y'
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
          (Module.length R (G.H0 𝒦R)).toNat) ∧
    ∀ i : ℕ, Module.Finite K (GW.HSucc 𝔚 i) ∧
      Module.finrank K (GW.HSucc 𝔚 i) =
        ∑ y' ∈ TV,
          letI y : A := κ.base y'
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
          (Module.length R (G.HSucc 𝒦R i)).toNat := by sorry
