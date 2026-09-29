-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_eulerChar_mumfordBundle_tensor_pullback_snd_eq_neg_one_pow_mul_finrank_of_forall_iff_isInStabilizer
-- name    : AlgebraicGeometry.Polarisation.eulerChar_mumfordBundle_tensor_pullback_snd_eq_neg_one_pow_mul_finrank_of_forall_iff_isInStabilizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/33ed9db0-2d4c-5a4d-8bb9-72c326a982be
-- title:
--   Euler characteristic of a twisted Mumford bundle
-- statement:
--   Let $K$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} K$ a morphism, equipped with a relative group law $L$ for $f$, that is, a functorial group structure on the sets of $f$-sections $\{\varphi : T \to A \mid \varphi \circ f = t\}$ over morphisms $t : T \to \operatorname{Spec} K$, compatible with base change; assume $L$ is commutative, and that $f$ satisfies `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and a relative group law for $f$ exists. Let $g$ be a natural number with $f$ smooth of relative dimension $g$, and let $M$ be an $\mathcal{O}_A$-module which is invertible in the sense that every point of $A$ has a neighbourhood $U$ with $M|_U$ isomorphic to the unit module of $U$. Let $\kappa : K_M \to A$ be a closed immersion with $\kappa$ followed by $f$ finite, and assume that for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} K$ and every $f$-section $x$ over $t$, the morphism $x$ factors through $\kappa$ if and only if $L$-translation by $x$ stabilises $M$, in the sense that the pullback of $M$ along $L.mulRight\ t\ x$ and the pullback of $M$ along the first projection of $A \times_{\operatorname{Spec} K} \operatorname{Spec} R$ are locally isomorphic over the second projection. Let $N$ be a further invertible $\mathcal{O}_A$-module, and let $\mathfrak{W}$ be an ordered affine cover of $A \times_{\operatorname{Spec} K} A$ (a finite linearly ordered family of affine opens with supremum $\top$). Then the Euler characteristic, computed as the alternating sum $\sum_{i < \#\mathfrak{W}.\iota} (-1)^i \dim_K$ of the Čech modules attached to $\mathfrak{W}$ and to the presheaf of sections of the Mumford bundle $\Lambda(M) = \mathrm{add}^{*}M \otimes (p_1^{*}M^{\vee} \otimes p_2^{*}M^{\vee})$ twisted by $p_2^{*}N$, over the structure morphism $p_1$ followed by $f$, equals $(-1)^g$ times the $K$-rank of $\kappa$ followed by $f$ at the closed point of $\operatorname{Spec} K$.
--
--   This is the Riemann–Roch-type index computation for the Mumford bundle on an abelian variety, in the form $\chi(\Lambda(M) \otimes p_2^{*}N) = (-1)^g \deg K(M)$, the twist by $p_2^{*}N$ being harmless; the hypothesis on $\kappa$ expresses that $K_M \hookrightarrow A$ represents the stabiliser of $M$ and is finite over $K$. It feeds the product formula [`GoodReductionJacobian.AbelianSchemePropertyBundle.eulerChar_mul_eulerChar_dual_eq_neg_one_pow_mul_finrank_of_forall_iff_isInStabilizer`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.eulerChar_mul_eulerChar_dual_eq_neg_one_pow_mul_finrank_of_forall_iff_isInStabilizer).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_eulerChar_mumfordBundle_tensor_pullback_snd_eq_neg_one_pow_mul_finrank_of_forall_iff_isInStabilizer.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.eulerChar_mumfordBundle_tensor_pullback_snd_eq_neg_one_pow_mul_finrank_of_forall_iff_isInStabilizer
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    {KM : Scheme.{0}} (κ : KM ⟶ A) (hκ : IsClosedImmersion κ) (hfin : IsFinite (κ ≫ f))
    (hK : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      (∃ x₀ : Spec (CommRingCat.of R) ⟶ KM, x₀ ≫ κ = x.1) ↔ L.IsInStabilizer M t x)
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N) (𝔚 : (pullback f f).OrderedAffineCover) :
    (OModulePresheaf.ofModules (pullback.fst f f ≫ f)
        (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N)).eulerChar 𝔚 =
      (-1) ^ g * ((κ ≫ f).finrank (IsLocalRing.closedPoint K) : ℤ) := by sorry
