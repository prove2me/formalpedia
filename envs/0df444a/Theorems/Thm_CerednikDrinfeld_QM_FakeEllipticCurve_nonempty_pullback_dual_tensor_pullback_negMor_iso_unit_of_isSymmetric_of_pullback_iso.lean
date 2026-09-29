-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_pullback_dual_tensor_pullback_negMor_iso_unit_of_isSymmetric_of_pullback_iso
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_pullback_dual_tensor_pullback_negMor_iso_unit_of_isSymmetric_of_pullback_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/12a73131-39e1-54f7-9a99-f972c2d6ae39
-- title:
--   Triviality of t^*(mathcal L₁'^∨⊗[-1]^*mathcal L₁') over a symmetric base
-- statement:
--   Fix primes $q,q'$ with $q'\neq q$, rationals $a,b$ such that the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ is indefinite and ramified exactly at $q$ and $q'$ (that is, $0<a$ or $0<b$, and for every finite place $v$ of $\mathbb Q$ the base change of the algebra to the $v$-adic completion is a division algebra precisely when $v$ divides $q$ or $q'$), a maximal order $\Lambda$, an element $\mu\in\Lambda$ with $\mu^{2}=-(qq')\cdot 1$, and a map $\mathrm{star}\colon\Lambda\to\Lambda$ satisfying $\mu\,\mathrm{star}(x)=\bar x\mu$; fix a natural number $N$, a commutative ring $S$ and a fake elliptic curve $E$ over $S$ with level data $(\Lambda,N)$, with structure morphism $E.f\colon A\to\operatorname{Spec} S$ and relative group law $E.L$. Let $R_1$ be a local noetherian commutative ring and $R_0$ a nontrivial commutative ring, both $S$-algebras, let $\varphi\colon R_1\to R_0$ be a surjective $S$-algebra map whose kernel annihilates the maximal ideal of $R_1$, and let $t$ be a morphism from the base change $A_{R_0}=A\times_{\operatorname{Spec} S}\operatorname{Spec} R_0$ to $A_{R_1}$ commuting with the first projections and with the second projections up to $\operatorname{Spec}\varphi$. Let $L_1$ and $L_0$ be relative group laws on $A_{R_1}\to\operatorname{Spec} R_1$ and $A_{R_0}\to\operatorname{Spec} R_0$, each compatible with $E.L$ in the sense that the first projection carries the product of two points to the product of their images. Assume $2$ is a unit in $R_1$, let $\mathcal L_0$ be an invertible module on $A_{R_0}$ that is symmetric for $L_0$ (the pullback of $\mathcal L_0$ along the inversion morphism $\mathrm{negMor}$ of $L_0$ and $\mathcal L_0$ become isomorphic after restriction to the preimage of some open neighbourhood of each point of $\operatorname{Spec} R_0$), and let $\mathcal L_1'$ be an invertible module on $A_{R_1}$ with $t^{*}\mathcal L_1'\cong\mathcal L_0$. Then $t^{*}\bigl(\mathcal L_1'^{\vee}\otimes \mathrm{negMor}(L_1)^{*}\mathcal L_1'\bigr)$ is isomorphic to the unit module on $A_{R_0}$, where the dual is the internal hom into the unit.
--
--   This is the statement that the antisymmetric part of an invertible lift dies after pullback along the transition morphism: it measures the failure of a lift $\mathcal L_1'$ of a symmetric bundle to be symmetric, and is the step used to correct such a lift. It feeds into the construction of a symmetric lift of a polarisation bundle along a small surjection of $S$-algebras in the deformation theory of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_pullback_dual_tensor_pullback_negMor_iso_unit_of_isSymmetric_of_pullback_iso.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_pullback_dual_tensor_pullback_negMor_iso_unit_of_isSymmetric_of_pullback_iso
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S)

    (R₁ R₀ : Type) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁]
    [CommRing R₀] [Nontrivial R₀] [Algebra S R₁] [Algebra S R₀]
    (φ : R₁ →ₐ[S] R₀) (hφ : Function.Surjective φ)
    (hsmall : ∀ x ∈ RingHom.ker φ.toRingHom, ∀ m ∈ IsLocalRing.maximalIdeal R₁, x * m = 0)

    (t : pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))
    (ht₁ : t ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))
    (ht₂ : t ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) =
      pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))

    (L₁ : RelativeGroupLaw R₁ (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))))
    (hL₁ : ∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R₁))
        (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))),
        (L₁.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) =
          (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))
            ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (L₀ : RelativeGroupLaw R₀ (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))))
    (hL₀ : ∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R₀))
        (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))),
        (L₀.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) =
          (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))
            ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (h2 : IsUnit (2 : R₁))
    (𝓛₀ : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))).Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) (hsym₀ : IsSymmetric (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))) L₀ 𝓛₀)
    (𝓛₁' : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))).Modules) (hinv₁' : Scheme.Modules.IsInvertible 𝓛₁') (hiso' : Nonempty ((Scheme.Modules.pullback t).obj 𝓛₁' ≅ 𝓛₀)) :
    Nonempty ((Scheme.Modules.pullback t).obj
        (Scheme.Modules.dual 𝓛₁' ⊗ (Scheme.Modules.pullback (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁)).obj 𝓛₁') ≅ 𝟙_ _) := by sorry
