-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_exists_bijective_place_restrictAlong_eq_of_not_dvd_of_two_mul_dvd
-- name    : CerednikDrinfeld.QM.ModuliTowerWitnessD.exists_bijective_place_restrictAlong_eq_of_not_dvd_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/cc8680ca-b6d6-5e9d-bfa9-5658c6d8b74e
-- title:
--   A place bijection exchanging the two tower legs at ℓ
-- statement:
--   Fix natural numbers $N \neq 0$ and primes $q \neq q'$, neither dividing $N$, and a natural number $D$ divisible by $2Nqq'$. Let $a,b \in \mathbb{Q}$ satisfy `IsIndefiniteRamifiedExactlyAt`, i.e. $a>0$ or $b>0$ and, for every height-one prime $v$ of the integers of $\mathbb{Q}$, the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$; let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is a maximal order (an order — containing $1$, multiplicatively closed, $\mathbb{Q}$-spanning, finitely generated — maximal among orders). Let $\bar F$ be a field over $\overline{\mathbb{Q}}$ that is a curve over $\overline{\mathbb{Q}}$ in the sense of `IsCurveOver` and essentially of finite type. Over $\mathrm{Spec}$ of $\mathbb{Z}[1/D]$ one is given a scheme $X$ with structure morphism $\pi_X$, a $\overline{\mathbb{Q}}$-point $\bar s$ of the base, and a point-law `pt` sending each fake elliptic curve with level $N$ structure over a ring $S$, together with a base morphism $s$, to an $s$-point of $X$; `pt` is assumed constant on isomorphism classes, compatible with base change along ring maps over the base, and, over algebraically closed fields, surjective onto the points of $X$ and injective up to isomorphism. Further data: a curve model $\mathfrak{M}$ of $\bar F$ over $\overline{\mathbb{Q}}$ with an isomorphism $e_{\mathfrak{M}}$ onto the fibre product of $\pi_X$ and $\bar s$ whose composition with the second projection is the structure morphism of $\mathfrak{M}$; a semilinear Galois action `gal` of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $\bar F$; tower data $\mathbb{T}$ assigning to each prime $\ell \notin \{q,q'\}$ a curve field $\mathbb{T}.F\,\ell$ over $\overline{\mathbb{Q}}$ together with two finite integral $\overline{\mathbb{Q}}$-algebra maps $\mathbb{T}.\varphi(\ell,0), \mathbb{T}.\varphi(\ell,1) : \bar F \to \mathbb{T}.F\,\ell$; semilinear Galois actions `galT` on each $\mathbb{T}.F\,\ell$; and semilinear automorphisms $W$, $WT$ indexed by `Fin 2`. Finally a witness `tw` of type `ModuliTowerWitnessD`, which records representatives `rep` of places of $\bar F$ by fake elliptic curves over $\overline{\mathbb{Q}}$ matching `pt` with the curve model, representatives `repT` of places of $\mathbb{T}.F\,\ell$ by fake elliptic curves with extra level structure at $\ell$ that are surjective and injective up to isomorphism, the compatibility of `gal`, `galT`, $W$, $WT$ with their actions on $\overline{\mathbb{Q}}$, the identification of the restriction along the leg $0$ with forgetting the extra level, and further compatibilities. Then, for each prime $\ell \notin \{q,q'\}$ with $\ell \nmid N$, there is a bijection $\theta$ of the set of places of $\mathbb{T}.F\,\ell$ over $\overline{\mathbb{Q}}$ such that for every place $R$ the restriction of $\theta(R)$ along $\mathbb{T}.\varphi(\ell,0)$ equals the restriction of $R$ along $\mathbb{T}.\varphi(\ell,1)$.
--
--   This is the place-theoretic form of the Fricke-type involution $w_\ell$ on the moduli problem of pairs $(E,K)$ with $K$ an $\ell$-level subgroup, which interchanges the two degeneracy legs of the Hecke tower at a prime $\ell \nmid N$. It is used in the comparison of the degrees of the two legs, namely in `finrankAlong_eq_arrowDegree_of_pt_pullback_of_two_mul_dvd_of_squarefree`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_exists_bijective_place_restrictAlong_eq_of_not_dvd_of_two_mul_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
open AlgebraicCurve

theorem CerednikDrinfeld.QM.ModuliTowerWitnessD.exists_bijective_place_restrictAlong_eq_of_not_dvd_of_two_mul_dvd
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
    (ℓ : HeckeTower.AwayPrime q q') (hℓN : ¬ ((ℓ.1 : ℕ) ∣ N)) :
    ∃ θ : Place (AlgebraicClosure ℚ) (𝕋.F ℓ) → Place (AlgebraicClosure ℚ) (𝕋.F ℓ), Function.Bijective θ ∧
      ∀ R : Place (AlgebraicClosure ℚ) (𝕋.F ℓ),
        (θ R).restrictAlong (𝕋.φ (ℓ, 0)) (𝕋.integral (ℓ, 0)) = R.restrictAlong (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 1)) := by sorry
