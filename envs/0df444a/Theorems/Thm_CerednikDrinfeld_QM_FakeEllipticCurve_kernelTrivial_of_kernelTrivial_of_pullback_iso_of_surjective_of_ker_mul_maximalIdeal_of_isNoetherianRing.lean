-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_of_kernelTrivial_of_pullback_iso_of_surjective_of_ker_mul_maximalIdeal_of_isNoetherianRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.kernelTrivial_of_kernelTrivial_of_pullback_iso_of_surjective_of_ker_mul_maximalIdeal_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/b0c14385-6ef7-59ca-a80d-6e334d56320b
-- title:
--   Trivial kernel descends along a small surjection
-- statement:
--   Fix distinct primes $q\neq q'$, rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ is indefinite (i.e. $0<a$ or $0<b$) and the completion at a place of $\mathbb Q$ is a division algebra exactly at the places above $q$ or $q'$, a maximal order $\Lambda\subset\mathbb H[\mathbb Q,a,b]$ (an order maximal among orders for inclusion), an element $\mu\in\Lambda$ with $\mu^2=-(qq')\cdot 1$, and a map $\star\colon\Lambda\to\Lambda$ satisfying $\mu\,(x^\star)=\bar x\,\mu$ for all $x\in\Lambda$; fix $N\in\mathbb N$, a commutative ring $S$ and a `FakeEllipticCurve Λ N S` denoted $E$, with structure morphism $E.f\colon A\to\operatorname{Spec}S$ and relative group law $E.L$. Let $\varphi\colon R_1\to R_0$ be a surjective $S$-algebra homomorphism with $R_1$ Noetherian local, $R_0$ nontrivial, and $x\cdot m=0$ for all $x\in\ker\varphi$ and all $m$ in the maximal ideal of $R_1$. Let $t$ be a morphism from the base change of $E.f$ to $R_0$ to its base change to $R_1$ commuting with the first projections and intertwining the second projections via $\operatorname{Spec}\varphi$. Let $L_1$, $L_0$ be relative group laws on the two base changes whose multiplications are compatible, through the first projections, with that of $E.L$. Let $\mathcal L_0$ be a module on the $R_0$-base change whose kernel is trivial for $L_0$, in the sense that for every commutative ring $R$, every $t'\colon\operatorname{Spec}R\to\operatorname{Spec}R_0$ and every section $x$ over $t'$, if the pullback along the slice at $x$ of the Mumford bundle $m^*\mathcal L_0\otimes p_1^*\mathcal L_0^\vee\otimes p_2^*\mathcal L_0^\vee$ is, locally on the base $\operatorname{Spec}R$, isomorphic to the unit module, then $x=L_0.\mathrm{one}\,t'$. Let $\mathcal L_1$ be an invertible module on the $R_1$-base change with $t^*\mathcal L_1\cong\mathcal L_0$. Then $\mathcal L_1$ has trivial kernel for $L_1$ in the same sense.
--
--   This is the kernel, or $K(\mathcal L)=e$, clause in the permanence of a polarisation datum along a small thickening of the base: triviality of the Mumford kernel descends from the quotient $R_0$ to the Noetherian local ring $R_1$ for a given lift of the invertible module, representability of the kernel subscheme over a Noetherian base being supplied by the abelian-scheme property bundle of the fake elliptic curve. It feeds the construction of canonical polarisation data on fake elliptic curves over Artinian local bases with prescribed residue characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_of_kernelTrivial_of_pullback_iso_of_surjective_of_ker_mul_maximalIdeal_of_isNoetherianRing.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.kernelTrivial_of_kernelTrivial_of_pullback_iso_of_surjective_of_ker_mul_maximalIdeal_of_isNoetherianRing
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

    (𝓛₀ : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))).Modules)
    (hker₀ : KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))) L₀ 𝓛₀)
    (𝓛₁ : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))).Modules)
    (hinv₁ : Scheme.Modules.IsInvertible 𝓛₁) (hiso : Nonempty ((Scheme.Modules.pullback t).obj 𝓛₁ ≅ 𝓛₀)) :
    KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁ 𝓛₁ := by sorry
