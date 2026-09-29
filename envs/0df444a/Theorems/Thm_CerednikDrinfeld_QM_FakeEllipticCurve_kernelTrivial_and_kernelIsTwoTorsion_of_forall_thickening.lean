-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_and_kernelIsTwoTorsion_of_forall_thickening
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.kernelTrivial_and_kernelIsTwoTorsion_of_forall_thickening
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/63db0d87-62ba-5425-95ba-d0b2b3fe24ea
-- title:
--   Kernel conditions pass from thickenings to complete local base
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite and ramified exactly at $q,q'$ in the sense of `IsIndefiniteRamifiedExactlyAt`: $0<a$ or $0<b$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit precisely when $q\in v$ or $q'\in v$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, $\mu\in\Lambda$ with $\mu^2=-(qq')\cdot 1$, and $\mathrm{star}:\Lambda\to\Lambda$ with $\mu\cdot\mathrm{star}(x)=\bar{x}\mu$. Let $N$ be a natural number, $S$ a commutative ring and $E$ a `FakeEllipticCurve` for $\Lambda$, $N$ over $S$, with structure morphism $E.f$ and group law $E.L$. Let $R$ be a local Noetherian $S$-algebra, adically complete for its maximal ideal and with algebraically closed residue field. For each $k$ let $j\,k$ be a morphism from the base change of $E.f$ to $R/\mathfrak{m}^{k+1}$ to the base change to $R$, compatible with the first projections (hj₁) and intertwining the second projections with $\operatorname{Spec}$ of the quotient map $R\to R/\mathfrak{m}^{k+1}$ (hj₂). Let $L'$ be a relative group law on the projection $A_R\to\operatorname{Spec} R$ whose multiplication of two points over any base is carried by the first projection to the $E.L$-multiplication of their images, and let $\mathcal{L}_0,\mathcal{L}$ be invertible modules on $A_R$. Assume that for every $k$ and every relative group law $L_k$ on $A_{R/\mathfrak{m}^{k+1}}\to\operatorname{Spec}(R/\mathfrak{m}^{k+1})$ compatible with $E.L$ in the same way, the pullback $(j\,k)^*\mathcal{L}_0$ satisfies `KernelTrivial` and $(j\,k)^*\mathcal{L}$ satisfies `KernelIsTwoTorsion`. Then $\mathcal{L}_0$ satisfies `KernelTrivial` and $\mathcal{L}$ satisfies `KernelIsTwoTorsion` for $L'$ over $R$. Here `KernelTrivial` for a bundle $\mathcal{M}$ asserts that for every commutative ring $R_1$, every $t:\operatorname{Spec} R_1\to\operatorname{Spec} R$ and every section $x$ over $t$, local triviality on the base of the pullback along `sliceAt` of the Mumford bundle $m^*\mathcal{M}\otimes \mathrm{pr}_1^*\mathcal{M}^{\vee}\otimes\mathrm{pr}_2^*\mathcal{M}^{\vee}$ forces $x$ to be the identity section, and `KernelIsTwoTorsion` asserts that this local triviality holds if and only if $x+x$ is the identity section.
--
--   This is the statement that the conditions $K(\mathcal{L}_0)=e$ and $K(\mathcal{L})=A[2]$ on the stabiliser subschemes of two invertible modules on a fake elliptic curve descend from all infinitesimal thickenings $R/\mathfrak{m}^{k+1}$ to a complete local Noetherian base $R$. It feeds the construction of the canonical polarisation datum, being cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.kernelTrivial_isSymmetric_isCanonicalPolData_of_forall_thickening`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.kernelTrivial_isSymmetric_isCanonicalPolData_of_forall_thickening).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_and_kernelIsTwoTorsion_of_forall_thickening.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.kernelTrivial_and_kernelIsTwoTorsion_of_forall_thickening
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsAlgClosed (IsLocalRing.ResidueField R)] [Algebra S R]
    (j : ∀ k : ℕ, pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))
    (hj₁ : ∀ k, j k ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))
    (hj₂ : ∀ k, j k ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
      pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (k + 1)))))
    (L' : RelativeGroupLaw R (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))))
    (hL' : (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (𝓛₀ 𝓛 : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))).Modules)
    (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hk : ∀ (k : ℕ) (Lk : RelativeGroupLaw (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))),
            (Lk.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))))) Lk ((Scheme.Modules.pullback (j k)).obj 𝓛₀) ∧
        KernelIsTwoTorsion (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))))) Lk ((Scheme.Modules.pullback (j k)).obj 𝓛)) :
    KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L' 𝓛₀ ∧
    KernelIsTwoTorsion (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L' 𝓛 := by sorry
