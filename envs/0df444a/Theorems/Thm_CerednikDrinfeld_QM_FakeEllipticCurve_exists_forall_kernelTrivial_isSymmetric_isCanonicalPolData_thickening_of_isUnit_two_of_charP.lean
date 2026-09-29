-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_kernelTrivial_isSymmetric_isCanonicalPolData_thickening_of_isUnit_two_of_charP
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_kernelTrivial_isSymmetric_isCanonicalPolData_thickening_of_isUnit_two_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/76676d93-e35c-57b7-bd6c-2a1c6f30bae0
-- title:
--   Compatible tower of symmetric principal roots on thickenings
-- statement:
--   Fix primes $q \ne q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'` (that is, $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the base change of the algebra to the $v$-adic completion has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$); let $\Lambda$ be a maximal order (an order maximal among orders), $\mu \in \Lambda$ with $\mu^2 = -(qq')\cdot 1$, and $star : \Lambda \to \Lambda$ satisfying $\mu \cdot star(x) = \bar{x}\mu$. Let $N$ be a natural number, $S$ a commutative ring and $E$ a fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ data, with structure morphism $E.f : A \to \operatorname{Spec} S$ and relative group law $E.L$. Let $R$ be a local Noetherian $S$-algebra, complete for the maximal-ideal adic topology, with algebraically closed residue field of characteristic the prime $p$, and with $2$ invertible in $R$. Write $A_k$ for the pullback of $E.f$ along $\operatorname{Spec}(S \to R/\mathfrak{m}^{k+1})$ and $A_R$ for the pullback along $\operatorname{Spec}(S \to R)$. One is given morphisms $j_k : A_k \to A_R$ compatible with the first projection and with the second projection up to $\operatorname{Spec}$ of the reduction $R \to R/\mathfrak{m}^{k+1}$, and transition morphisms $t_k : A_k \to A_{k+1}$ compatible with the first projections and satisfying $j_{k+1} \circ t_k = j_k$. The conclusion asserts the existence of modules $\mathcal{L}_k$ on $A_k$ such that each $\mathcal{L}_k$ is invertible (locally on $A_k$ isomorphic to the unit module), the pullback of $\mathcal{L}_{k+1}$ along $t_k$ is isomorphic to $\mathcal{L}_k$ for every $k$, and, for every $k$ and every relative group law $L_k$ on $A_k \to \operatorname{Spec}(R/\mathfrak{m}^{k+1})$ whose multiplication is compatible with $E.L$ under the first projection (on sections over every base scheme), one has: the kernel of $\mathcal{L}_k$ is trivial, in the sense that a section of $A_k$ over an affine base whose slice of the Mumford bundle of $(L_k,\mathcal{L}_k)$ is locally isomorphic on the base to the unit must be the identity section; $\mathcal{L}_k$ is symmetric, i.e. its pullback along the inversion morphism of $L_k$ is locally isomorphic on the base to $\mathcal{L}_k$; and the module $\mathcal{L}_k \otimes [-1]^*\mathcal{L}_k$ is canonical polarisation data for $L_k$, the $\Lambda$-action induced from $E.act$ by pullback, and $star$ — that is, it is invertible, symmetric, has kernel killed by $2$, becomes, after a faithfully flat base change and for any compatible group law there, of the form $\mathcal{L}_0 \otimes [-1]^*\mathcal{L}_0$ with $\mathcal{L}_0$ invertible of trivial kernel, has positive $H^0$-rank on all geometric fibres over algebraically closed fields, and is Rosati-compatible with the action and $star$.
--
--   This is the inductive half of the construction, over a complete local base with $2$ invertible, of a compatible system of symmetric principal roots of the canonical polarisation on the $\mathfrak{m}$-adic infinitesimal thickenings of a fake elliptic curve: the case $k=0$ comes from the algebraically closed residue field and the step from deformation of the polarisation datum along $R/\mathfrak{m}^{k+2} \twoheadrightarrow R/\mathfrak{m}^{k+1}$. It feeds the passage to a single invertible module over $R$ by Grothendieck existence, used in the Čerednik–Drinfeld analysis of the quaternionic moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_kernelTrivial_isSymmetric_isCanonicalPolData_thickening_of_isUnit_two_of_charP.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_kernelTrivial_isSymmetric_isCanonicalPolData_thickening_of_isUnit_two_of_charP
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsAlgClosed (IsLocalRing.ResidueField R)] [Algebra S R]
    (h2 : IsUnit (2 : R))
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]

    (j : ∀ k : ℕ, pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))
    (hj₁ : ∀ k, j k ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))
    (hj₂ : ∀ k, j k ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
      pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (k + 1)))))
    (t : ∀ k : ℕ, pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1 + 1))))))
    (ht₁ : ∀ k, t k ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1 + 1))))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))
    (ht : ∀ k, t k ≫ j (k + 1) = j k) :
    ∃ 𝓛k : ∀ k : ℕ, (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))))).Modules,
      (∀ k, Scheme.Modules.IsInvertible (𝓛k k)) ∧
      (∀ k, Nonempty ((Scheme.Modules.pullback (t k)).obj (𝓛k (k + 1)) ≅ 𝓛k k)) ∧
      (∀ (k : ℕ) (Lk : RelativeGroupLaw (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))),
            (Lk.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))))) Lk (𝓛k k) ∧
        IsSymmetric (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))))) Lk (𝓛k k) ∧
        CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))))) Lk
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star (𝓛k k ⊗ (Scheme.Modules.pullback (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))))) Lk)).obj (𝓛k k))) := by sorry
