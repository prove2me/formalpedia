-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_isSymmetric_isCanonicalPolData_of_forall_thickening
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.kernelTrivial_isSymmetric_isCanonicalPolData_of_forall_thickening
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/b61428d6-d1eb-5957-838e-b0db2b3efa31
-- title:
--   Canonical polarisation datum passes from thickenings to complete local base
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds for $\mathbb H[\mathbb Q,a,b]$: $0<a$ or $0<b$, and for every height-one prime $v$ of the integers of $\mathbb Q$ the completion $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb Z$-submodule of $\mathbb H[\mathbb Q,a,b]$ which is an order maximal among orders, $\mu\in\Lambda$ with $\mu^{2}=-(qq')\cdot 1$, and $star:\Lambda\to\Lambda$ a map with $\mu\,star(x)=\bar x\,\mu$ for all $x\in\Lambda$. Let $N\in\mathbb N$, $S$ a commutative ring and $E$ a `FakeEllipticCurve` for $\Lambda$, $N$ over $S$, with structure morphism $E.f$, relative group law $E.L$ and $\Lambda$-action $E.act$. Let $R$ be a local Noetherian $S$-algebra, complete for the $\mathfrak m$-adic topology, with algebraically closed residue field; write $A_R$ for the base change of $E.f$ along $\operatorname{Spec}(S\to R)$ and $A_k$ for the base change along $\operatorname{Spec}(S\to R/\mathfrak m^{k+1})$. Given morphisms $j_k : A_k \to A_R$ commuting with the first projections (hj₁) and compatible with the second projections through $\operatorname{Spec}$ of the reduction $R\to R/\mathfrak m^{k+1}$ (hj₂); a relative group law $L'$ on $A_R\to\operatorname{Spec} R$ whose multiplication is carried by the first projection to that of $E.L$ (hL'); and an invertible module $\mathcal L_0$ on $A_R$. Assume (hk) that for every $k$ and every relative group law $L_k$ on $A_k$ compatible with $E.L$ in the same sense, there is a module $\mathcal M$ on $A_k$ with $j_k^{*}\mathcal L_0\cong\mathcal M$ such that `KernelTrivial` holds for $(A_k,L_k,\mathcal M)$, i.e. any point $x$ of $A_k$ over any base change for which the slice of the Mumford bundle of $\mathcal M$ is locally isomorphic on the base to the unit module equals the identity point; `IsSymmetric` holds, i.e. $[-1]^{*}\mathcal M$ is locally isomorphic on the base to $\mathcal M$; and `IsCanonicalPolData` holds for $A_k$, $L_k$, the $\Lambda$-action obtained from $E.act$ by base change, the involution $star$ and the module $\mathcal M\otimes[-1]^{*}\mathcal M$. The conclusion is that the same three properties hold over $R$ itself: `KernelTrivial` for $(A_R,L',\mathcal L_0)$, `IsSymmetric` for $(A_R,L',\mathcal L_0)$, and `IsCanonicalPolData` for $A_R$, $L'$, the base-changed $\Lambda$-action, $star$, and $\mathcal L_0\otimes[-1]^{*}\mathcal L_0$ — the last unfolding to invertibility, symmetry, two-torsion kernel, the existence of a faithfully flat $R$-algebra over which compatible group laws admit a kernel-trivial invertible square root, positivity of the geometric fibre $H^{0}$-rank, and Rosati compatibility with the action and $star$.
--
--   This is the limit-passage step in the construction of a canonical polarisation datum on a fake elliptic curve over a complete local base: all three conditions are verified on the infinitesimal thickenings $A_{R/\mathfrak m^{k+1}}$ and transported to $A_R$. It is used by the existence theorem [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_kernelTrivial_isSymmetric_isCanonicalPolData_tensor_pullback_negMor_of_isAdicComplete_of_isUnit_two_of_charP`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_kernelTrivial_isSymmetric_isCanonicalPolData_tensor_pullback_negMor_of_isAdicComplete_of_isUnit_two_of_charP) in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_isSymmetric_isCanonicalPolData_of_forall_thickening.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.kernelTrivial_isSymmetric_isCanonicalPolData_of_forall_thickening
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
    (𝓛₀ : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))).Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (hk : ∀ (k : ℕ) (Lk : RelativeGroupLaw (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))),
            (Lk.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓜 : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))))).Modules, Nonempty ((Scheme.Modules.pullback (j k)).obj 𝓛₀ ≅ 𝓜) ∧
          KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))))) Lk 𝓜 ∧
          IsSymmetric (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))))) Lk 𝓜 ∧
          CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))))) Lk
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star (𝓜 ⊗ (Scheme.Modules.pullback (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))))) Lk)).obj 𝓜)) :
    KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L' 𝓛₀ ∧
    IsSymmetric (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L' 𝓛₀ ∧
    CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L'
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L')).obj 𝓛₀) := by sorry
