-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_exists_finite_restrictAlong_phi_injOn_of_two_mul_dvd
-- name    : CerednikDrinfeld.QM.ModuliTowerWitnessD.exists_finite_restrictAlong_phi_injOn_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/3c3be8da-d8e2-5f04-b62e-0c430df31938
-- title:
--   Degeneracy restrictions separate places off a finite set
-- statement:
--   Fix natural numbers $N \neq 0$ and primes $q, q'$ with $q \nmid N$, $q' \nmid N$ and $q' \neq q$, and a natural number $D$ divisible by $2Nqq'$. Let $a, b \in \mathbb{Q}$ satisfy `IsIndefiniteRamifiedExactlyAt`, i.e. $a > 0$ or $b > 0$ and, for each height-one prime $v$ of the integers of $\mathbb{Q}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$; let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be an order maximal among the orders containing it. Let $\bar F$ be a field which is a curve over $\overline{\mathbb{Q}}$ (principal divisors, finite residue extensions, $\Omega$ free of rank one) and essentially of finite type; let $\pi_X : X \to \operatorname{Spec} \mathbb{Z}[1/D]$ be a scheme over the localisation away from $D$, $\bar s$ a $\overline{\mathbb{Q}}$-point of that base, and $\mathrm{pt}$ an assignment sending a fake elliptic curve with $\Lambda$-action and level $N$ over a ring $S$, together with an $S$-point $s$ of the base, to a point of $X$ over $s$, assumed constant on isomorphism classes and, over algebraically closed fields, injective up to isomorphism. Let $\mathfrak{M}$ be a curve model of $\bar F$ over $\overline{\mathbb{Q}}$ with an isomorphism $e_{\mathfrak M}$ onto the pullback of $\pi_X$ along $\bar s$ compatible with the structure maps, $\mathrm{gal}$ a homomorphism from $\operatorname{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ to the semilinear automorphisms of $\bar F$, $\mathbb{T}$ a tower datum assigning to each prime $\ell \notin \{q,q'\}$ a curve field $F_\ell$ over $\overline{\mathbb{Q}}$ with two finite integral $\overline{\mathbb{Q}}$-algebra maps $\varphi_{\ell,0}, \varphi_{\ell,1} : \bar F \to F_\ell$, together with semilinear Galois actions $\mathrm{gal}_{\mathbb T}$ and semilinear automorphisms $W$, $W_{\mathbb T}$ as in the witness, and let $\mathrm{tw}$ be a `ModuliTowerWitnessD` for these data. Then for every prime $\ell \neq q, q'$ there is a finite set $S$ of places of $F_\ell$ over $\overline{\mathbb{Q}}$ such that any two places $P, P' \notin S$ whose restrictions along $\varphi_{\ell,0}$ agree and whose restrictions along $\varphi_{\ell,1}$ agree are equal.
--
--   This is the rigidity step saying that, off a finite exceptional set, a place of the level-$(N;\ell)$ field of the quaternionic moduli tower is determined by the pair of its restrictions along the two degeneracy maps. It feeds the proof that the image of the degeneracy maps generates the relevant field, via [`CerednikDrinfeld.QM.ModuliTowerWitnessD.closure_range_phi_eq_top_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.ModuliTowerWitnessD.closure_range_phi_eq_top_of_two_mul_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_exists_finite_restrictAlong_phi_injOn_of_two_mul_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
open AlgebraicCurve

theorem CerednikDrinfeld.QM.ModuliTowerWitnessD.exists_finite_restrictAlong_phi_injOn_of_two_mul_dvd
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) (hD : 2 * N * q * q' ∣ D)

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (E E' : FakeEllipticCurve Λ N S), FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')

    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) [CategoryTheory.IsIso e𝔐]
    (he𝔐 : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)
    (gal : ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT)
    :
    ∀ ℓ : HeckeTower.AwayPrime q q', ∃ S : Set (Place (AlgebraicClosure ℚ) (𝕋.F ℓ)), S.Finite ∧
      ∀ P P' : Place (AlgebraicClosure ℚ) (𝕋.F ℓ), P ∉ S → P' ∉ S →
        P.restrictAlong (𝕋.φ (ℓ, 0)) (𝕋.integral (ℓ, 0)) = P'.restrictAlong (𝕋.φ (ℓ, 0)) (𝕋.integral (ℓ, 0)) →
        P.restrictAlong (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 1)) = P'.restrictAlong (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 1)) →
        P = P' := by sorry
