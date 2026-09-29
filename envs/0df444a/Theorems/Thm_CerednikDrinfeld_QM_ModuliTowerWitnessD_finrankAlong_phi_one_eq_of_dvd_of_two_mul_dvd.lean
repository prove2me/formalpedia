-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_finrankAlong_phi_one_eq_of_dvd_of_two_mul_dvd
-- name    : CerednikDrinfeld.QM.ModuliTowerWitnessD.finrankAlong_phi_one_eq_of_dvd_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/29a8374a-8262-56da-96f2-2a2de3b19bc3
-- title:
--   Degree ℓ of the (ℓ,1) leg when ℓ ∣ N
-- statement:
--   Fix non-zero $N$ and primes $q \ne q'$ with $q \nmid N$, $q' \nmid N$, and a natural number $D$ divisible by $2Nqq'$. Let $a,b \in \mathbb{Q}$ satisfy `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $a > 0$ or $b > 0$, and for each height-one prime $v$ of the integers of $\mathbb{Q}$ the completion $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$; let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ that is an order maximal among orders. Let $Fbar$ be a field over $\overline{\mathbb{Q}}$ which is a curve over $\overline{\mathbb{Q}}$ (principal divisors, finite residue extensions at all places, $\Omega$ free of rank one) and essentially of finite type. Let $\pi_X : X \to \operatorname{Spec} \mathbb{Z}[1/D]$ be a scheme over the localisation away from $D$, $\bar s$ a $\overline{\mathbb{Q}}$-point of that base, and `pt` a law sending a fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ structure to a point of $X$ over $S$, assumed invariant under isomorphism, compatible with base change along ring maps, and bijective on isomorphism classes over algebraically closed fields. Let $\mathfrak{M}$ be a curve model of $Fbar$ over $\overline{\mathbb{Q}}$ together with an isomorphism $e_{\mathfrak{M}}$ from $\mathfrak{M}.C$ to the pullback of $\pi_X$ along $\bar s$ whose composite with the second projection is $\mathfrak{M}.\mathrm{toBase}$, let `gal` be a homomorphism from $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to semilinear automorphisms of $Fbar$ over $\overline{\mathbb{Q}}$, let $\mathbb{T}$ be tower data for $q,q'$ over $Fbar$ (fields $F_\ell$ for primes $\ell \ne q,q'$, curves over $\overline{\mathbb{Q}}$ and essentially of finite type, with finite integral $\overline{\mathbb{Q}}$-algebra maps $\varphi_\alpha : Fbar \to F_{\alpha.1}$ for each arrow $\alpha$), with Galois actions `galT` on each $F_\ell$ and involution data $W$, $WT$, and let `tw` be a `ModuliTowerWitnessD` for all these data. Then for every prime $\ell \ne q,q'$ dividing $N$, $F_\ell$ has dimension $\ell$ as a module over $Fbar$ via $\varphi_{(\ell,1)}$, that is, `finrankAlong` of $\mathbb{T}.\varphi\,(\ell,1)$ equals $\ell$.
--
--   This computes the degree of the second leg of the Hecke correspondence at a prime $\ell$ dividing the level $N$ on the Shimura curve attached to the indefinite quaternion algebra ramified exactly at $q,q'$; unlike the case $\ell \nmid N$ it cannot be obtained from the first leg by an involution exchanging the two legs. It feeds the identification of the degrees of both legs with the arrow degree in [`CerednikDrinfeld.QM.ModuliTowerWitnessD.finrankAlong_eq_arrowDegree_of_pt_pullback_of_two_mul_dvd_of_squarefree`](thm.html#CerednikDrinfeld.QM.ModuliTowerWitnessD.finrankAlong_eq_arrowDegree_of_pt_pullback_of_two_mul_dvd_of_squarefree).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_finrankAlong_phi_one_eq_of_dvd_of_two_mul_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
open AlgebraicCurve

theorem CerednikDrinfeld.QM.ModuliTowerWitnessD.finrankAlong_phi_one_eq_of_dvd_of_two_mul_dvd
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
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (x : SchemeHomOver s πX), ∃ E : FakeEllipticCurve Λ N k, pt k s E = x)
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
    (ℓ : HeckeTower.AwayPrime q q') (hℓN : (ℓ.1 : ℕ) ∣ N) :
    finrankAlong (AlgebraicClosure ℚ) (𝕋.φ (ℓ, 1)) = (ℓ.1 : ℕ) := by sorry
