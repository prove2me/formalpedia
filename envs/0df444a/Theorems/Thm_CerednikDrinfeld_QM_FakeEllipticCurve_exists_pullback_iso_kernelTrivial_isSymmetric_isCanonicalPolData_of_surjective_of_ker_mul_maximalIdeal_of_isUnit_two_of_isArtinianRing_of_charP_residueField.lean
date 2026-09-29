-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pullback_iso_kernelTrivial_isSymmetric_isCanonicalPolData_of_surjective_of_ker_mul_maximalIdeal_of_isUnit_two_of_isArtinianRing_of_charP_residueField
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_pullback_iso_kernelTrivial_isSymmetric_isCanonicalPolData_of_surjective_of_ker_mul_maximalIdeal_of_isUnit_two_of_isArtinianRing_of_charP_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/fb28c3fb-80c4-513e-bf4d-c61e5154ee47
-- title:
--   Lifting a symmetric canonical polarisation datum along a small surjection
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for a height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among orders, $\mu\in\Lambda$ with $\mu^2=-(qq')\cdot 1$, and $\star:\Lambda\to\Lambda$ a map with $\mu\,(x^\star)=\bar{x}\,\mu$ for all $x\in\Lambda$. Let $N\in\mathbb{N}$, $S$ a commutative ring and $E$ a fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ datum, with structure morphism $E.f:A\to\operatorname{Spec} S$ and relative group law $E.L$. Let $R_1$ be a local noetherian Artinian $S$-algebra with algebraically closed residue field of characteristic a prime $p$ and with $2\in R_1^{\times}$, let $R_0$ be a nontrivial $S$-algebra, and let $\varphi:R_1\to R_0$ be a surjective $S$-algebra map whose kernel is small, i.e. $x m=0$ for all $x\in\ker\varphi$ and all $m$ in the maximal ideal of $R_1$. Write $A_{R_i}$ for the pullback of $E.f$ along $\operatorname{Spec}$ of $R_i$, with its two projections. Let $t:A_{R_0}\to A_{R_1}$ be a morphism compatible with the projections to $A$ and with $\varphi$ on the bases, and let $L_1$, $L_0$ be relative group laws on $A_{R_1}\to\operatorname{Spec} R_1$ and $A_{R_0}\to\operatorname{Spec} R_0$ whose multiplications are compatible with that of $E.L$ under the projections to $A$. Assume given a module $\mathcal{L}_0$ on $A_{R_0}$ which is invertible (locally on $A_{R_0}$ isomorphic to the unit), has trivial kernel with respect to $L_0$ (any section of $A_{R_0}$ over a base change whose associated Mumford bundle is locally isomorphic on the base to the unit equals the identity section), is symmetric (the pullback along the inversion morphism of $L_0$ is locally isomorphic on the base to $\mathcal{L}_0$), and for which $\mathcal{L}_0\otimes[-1]^{*}\mathcal{L}_0$ is a canonical polarisation datum for $L_0$, the $\Lambda$-action obtained from $E$ by pullback, and $\star$. The conclusion asserts the existence of a module $\mathcal{L}_1$ on $A_{R_1}$ with $t^{*}\mathcal{L}_1\cong\mathcal{L}_0$, invertible, with trivial kernel with respect to $L_1$, symmetric, and such that $\mathcal{L}_1\otimes[-1]^{*}\mathcal{L}_1$ is a canonical polarisation datum for the same data over $R_1$.
--
--   This is the inductive step of the Serre–Tate style lifting of a polarised fake elliptic curve: it transports a principal symmetric line bundle, together with its canonical symmetrisation and the Rosati compatibility with the quaternionic action, across a small extension of Artinian local bases. It is used in the construction of the polarisation on the formal tower of thickenings, [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_kernelTrivial_isSymmetric_isCanonicalPolData_thickening_of_isUnit_two_of_charP`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_kernelTrivial_isSymmetric_isCanonicalPolData_thickening_of_isUnit_two_of_charP).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pullback_iso_kernelTrivial_isSymmetric_isCanonicalPolData_of_surjective_of_ker_mul_maximalIdeal_of_isUnit_two_of_isArtinianRing_of_charP_residueField.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_pullback_iso_kernelTrivial_isSymmetric_isCanonicalPolData_of_surjective_of_ker_mul_maximalIdeal_of_isUnit_two_of_isArtinianRing_of_charP_residueField
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S)
    (R₁ R₀ : Type) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [IsArtinianRing R₁] [IsAlgClosed (IsLocalRing.ResidueField R₁)]
    [CommRing R₀] [Nontrivial R₀] [Algebra S R₁] [Algebra S R₀]
    (φ : R₁ →ₐ[S] R₀) (hφ : Function.Surjective φ)
    (hsmall : ∀ x ∈ RingHom.ker φ.toRingHom, ∀ m ∈ IsLocalRing.maximalIdeal R₁, x * m = 0)
    (h2 : IsUnit (2 : R₁))
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R₁) p]
    (t : pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))
    (ht₁ : t ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))
    (ht₂ : t ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) = pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    (L₁ : RelativeGroupLaw R₁ (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))))
    (hL₁ : (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R₁))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))),
            (L₁.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (L₀ : RelativeGroupLaw R₀ (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))))
    (hL₀ : (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R₀))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))),
            (L₀.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (𝓛₀ : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))).Modules)
    (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀ ∧
      KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))) L₀ 𝓛₀ ∧
      IsSymmetric (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))) L₀ 𝓛₀ ∧
      CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))) L₀
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))) L₀)).obj 𝓛₀)) :
    ∃ 𝓛₁ : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))).Modules,
      Nonempty ((Scheme.Modules.pullback t).obj 𝓛₁ ≅ 𝓛₀) ∧
      Scheme.Modules.IsInvertible 𝓛₁ ∧
      KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁ 𝓛₁ ∧
      IsSymmetric (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁ 𝓛₁ ∧
      CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star (𝓛₁ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁)).obj 𝓛₁) := by sorry
