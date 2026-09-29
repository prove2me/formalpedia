-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isSymmetric_pullback_iso_of_isSymmetric_of_pullback_iso_of_isUnit_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isSymmetric_pullback_iso_of_isSymmetric_of_pullback_iso_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/70a7def3-4a99-548c-ac4b-deb5ea5e7bdd
-- title:
--   Symmetric lift of an invertible sheaf across a small thickening
-- statement:
--   Let $q\neq q'$ be primes and $a,b\in\mathbb Q$ such that the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the completed algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$; let $\Lambda$ be a maximal order (an order maximal among orders), $\mu\in\Lambda$ with $\mu^2=-(qq')\cdot 1$, and $\star:\Lambda\to\Lambda$ a map with $\mu\,\star x=\bar x\,\mu$ for all $x$. Fix $N\in\mathbb N$, a commutative ring $S$ and a fake elliptic curve $E$ for $\Lambda$ of level $N$ over $S$, with structure morphism $E.f$. Let $R_1$ be a local noetherian $S$-algebra, $R_0$ a nontrivial $S$-algebra, and $\varphi:R_1\to R_0$ a surjective $S$-algebra map whose kernel annihilates the maximal ideal of $R_1$ (a small thickening). Write $A_i$ for the base change `pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S Rᵢ)))`, and let $t:A_0\to A_1$ be a morphism compatible with the first projections and with the second projections up to $\mathrm{Spec}\,\varphi$. Let $L_1,L_0$ be relative group laws on $A_1,A_0$ over $R_1,R_0$ whose multiplications are compatible, after the first projection, with $E.L$. Assume $2$ is a unit in $R_1$, that $\mathcal L_0$ on $A_0$ is invertible (locally on $A_0$ isomorphic to the unit module) and symmetric, i.e. the pullback of $\mathcal L_0$ along the inversion morphism of $L_0$ is isomorphic to $\mathcal L_0$ after restriction over some open neighbourhood of each point of $\mathrm{Spec}\,R_0$, and that $\mathcal L_1'$ on $A_1$ is invertible with $t^*\mathcal L_1'\cong\mathcal L_0$. Then there exist invertible modules $\mathcal L_1$ and $d$ on $A_1$ with $t^*d\cong\mathbb 1$, $\mathcal L_1\cong\mathcal L_1'\otimes d$, $t^*\mathcal L_1\cong\mathcal L_0$, and $\mathcal L_1$ symmetric for $L_1$.
--
--   This is the deformation-theoretic step which makes a lift of a symmetric invertible sheaf across a small square-zero thickening symmetric again, by twisting the given lift by an invertible sheaf trivial on the closed thickening; invertibility of $2$ is what allows the obstruction class to be halved. It feeds the construction of a polarisation datum on a lift of a fake elliptic curve, used in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_pullback_iso_kernelTrivial_isSymmetric_isCanonicalPolData_of_surjective_of_ker_mul_maximalIdeal_of_isUnit_two_of_isArtinianRing_of_charP_residueField`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_pullback_iso_kernelTrivial_isSymmetric_isCanonicalPolData_of_surjective_of_ker_mul_maximalIdeal_of_isUnit_two_of_isArtinianRing_of_charP_residueField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isSymmetric_pullback_iso_of_isSymmetric_of_pullback_iso_of_isUnit_two.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isSymmetric_pullback_iso_of_isSymmetric_of_pullback_iso_of_isUnit_two
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
    ∃ (𝓛₁ d : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))).Modules),
      Scheme.Modules.IsInvertible 𝓛₁ ∧ Scheme.Modules.IsInvertible d ∧
      Nonempty ((Scheme.Modules.pullback t).obj d ≅ 𝟙_ _) ∧ Nonempty (𝓛₁ ≅ 𝓛₁' ⊗ d) ∧
      Nonempty ((Scheme.Modules.pullback t).obj 𝓛₁ ≅ 𝓛₀) ∧ IsSymmetric (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁ 𝓛₁ := by sorry
