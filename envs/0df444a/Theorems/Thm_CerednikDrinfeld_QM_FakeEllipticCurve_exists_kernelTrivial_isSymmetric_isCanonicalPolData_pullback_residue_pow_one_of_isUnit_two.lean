-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_kernelTrivial_isSymmetric_isCanonicalPolData_pullback_residue_pow_one_of_isUnit_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_kernelTrivial_isSymmetric_isCanonicalPolData_pullback_residue_pow_one_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/c7ef4fcd-0ccf-5a55-a094-8669e939636e
-- title:
--   Symmetric invertible root of the canonical polarisation over the residue field
-- statement:
--   Let $q \neq q'$ be primes, let $a, b \in \mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $0 < a$ or $0 < b$ and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q}, a, b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $q \in v$ or $q' \in v$; let $\Lambda \subseteq \mathbb{H}[\mathbb{Q}, a, b]$ be a $\mathbb{Z}$-submodule which is an order maximal among the orders containing it, let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq') \cdot 1$, and let $\mathrm{star} : \Lambda \to \Lambda$ satisfy $\mu \cdot \mathrm{star}(x) = \bar{x} \mu$ for all $x \in \Lambda$. Let $N \in \mathbb{N}$, let $S$ be a commutative ring and let $E$ be a `FakeEllipticCurve Λ N S`, with structure morphism $E.f : E.A \to \operatorname{Spec} S$, relative group law $E.L$ and $\Lambda$-action $E.\mathrm{act}$. Let $R$ be a commutative local $S$-algebra whose residue field is algebraically closed and in which $2$ is a unit. Put $R_0 := R/\mathfrak{m}^{0+1}$ and let $A_0 := E.A \times_{\operatorname{Spec} S} \operatorname{Spec} R_0$, with projections $\mathrm{fst}$ to $E.A$ and $\mathrm{snd}$ to $\operatorname{Spec} R_0$. Then there is an invertible module $\mathcal{L}_0$ on $A_0$ such that for every relative group law $L_0$ on $\mathrm{snd}$ over $R_0$ that is compatible with $E.L$ along $\mathrm{fst}$ — for all schemes $T$, all $t' : T \to \operatorname{Spec} R_0$ and all $T$-points $P, Q$ of $A_0$ over $t'$, the composite of $L_0.\mathrm{mul}\,t'\,P\,Q$ with $\mathrm{fst}$ equals the $E.L$-product of the images of $P$ and $Q$ under $\mathrm{fst}$ — the following hold: $\mathcal{L}_0$ has trivial kernel in the sense of `KernelTrivial` (any section $x$ over any affine base whose associated Mumford bundle pulled back along the slice at $x$ is locally trivial on the base is the identity section); $\mathcal{L}_0$ is symmetric, i.e. its pullback along the inversion morphism of $L_0$ is locally isomorphic to $\mathcal{L}_0$ on the base; and $\mathcal{L}_0 \otimes [-1]^{*}\mathcal{L}_0$ satisfies `IsCanonicalPolData` for $L_0$, the $\Lambda$-action on $A_0$ obtained from $E.\mathrm{act}$ by the universal property of the fibre product, and $\mathrm{star}$ — that is, it is invertible and symmetric, its kernel is two-torsion, it becomes a tensor product $\mathcal{L}' \otimes [-1]^{*}\mathcal{L}'$ with $\mathcal{L}'$ of trivial kernel after a faithfully flat base extension, all its geometric fibre $H^0$ ranks are positive, and it is Rosati-compatible with the action and $\mathrm{star}$.
--
--   Since $\mathfrak{m}^{0+1} = \mathfrak{m}$, the base $R_0$ here is the algebraically closed residue field of $R$, so this is the bottom level of the inductive tower of canonical polarisation data over the infinitesimal thickenings $R/\mathfrak{m}^{k+1}$ of the residue field; it provides the symmetric invertible square root $\mathcal{L}_0$ of the canonical polarisation on the reduction of a fake elliptic curve. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_kernelTrivial_isSymmetric_isCanonicalPolData_thickening_of_isUnit_two_of_charP`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_kernelTrivial_isSymmetric_isCanonicalPolData_thickening_of_isUnit_two_of_charP) as the base case of that recursion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_kernelTrivial_isSymmetric_isCanonicalPolData_pullback_residue_pow_one_of_isUnit_two.lean

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
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry CerednikDrinfeld NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open QuaternionAlgebra
open CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_kernelTrivial_isSymmetric_isCanonicalPolData_pullback_residue_pow_one_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S)
    (R : Type) [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] [Algebra S R]
    (h2 : IsUnit (2 : R)) :
    ∃ 𝓛₀ : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)))))).Modules, Scheme.Modules.IsInvertible 𝓛₀ ∧
      ∀ (L₀ : RelativeGroupLaw (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))))),
            (L₀.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)))))) L₀ 𝓛₀ ∧
        IsSymmetric (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)))))) L₀ 𝓛₀ ∧
        CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)))))) L₀
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)))))) L₀)).obj 𝓛₀) := by sorry
