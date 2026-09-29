-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_exists_curveModel_level_of_pt_pullback_of_two_mul_dvd_of_squarefree
-- name    : CerednikDrinfeld.QM.ModuliTowerWitnessD.exists_curveModel_level_of_pt_pullback_of_two_mul_dvd_of_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/8b8bbf28-2d09-5463-93ca-8f4473b096be
-- title:
--   Curve model for the ℓ-level layer of the QM tower
-- statement:
--   Fix a nonzero level $N$ and primes $q \neq q'$ with $q \nmid N$, $q' \nmid N$ and $N$ squarefree, and $D$ with $2Nqq' \mid D$. Let $a,b \in \mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies $0<a$ or $0<b$ and, for each finite place $v$ of $\mathbb{Q}$, has all nonzero elements of its $v$-adic completion invertible exactly when $v$ lies over $q$ or $q'$; let $\Lambda$ be a maximal order in it (an order: containing $1$, multiplicatively closed, spanning over $\mathbb{Q}$, finitely generated, and maximal among such). Let $\bar{F}$ be a field over $\mathbb{Q}^{\mathrm{alg}}$ which is a curve over it in the sense of `IsCurveOver` and essentially of finite type. Let $\pi_X : X \to \operatorname{Spec} \mathbb{Z}[1/D]$ be equipped with a rule `pt` sending a fake elliptic curve of level $N$ over a ring $S$ and a map $s : \operatorname{Spec} S \to \operatorname{Spec}\mathbb{Z}[1/D]$ to a point of $X$ over $s$, assumed invariant under isomorphism, compatible with pullback along ring homomorphisms, and bijective up to isomorphism on points with values in algebraically closed fields; let $\bar{s}$ be a $\mathbb{Q}^{\mathrm{alg}}$-point of the base. Let $\mathfrak{M}$ be a curve model of $\bar{F}$ over $\mathbb{Q}^{\mathrm{alg}}$ together with an isomorphism $e_{\mathfrak{M}} : \mathfrak{M}.C \to X \times_{\mathbb{Z}[1/D]} \operatorname{Spec}\mathbb{Q}^{\mathrm{alg}}$ over $\operatorname{Spec}\mathbb{Q}^{\mathrm{alg}}$, let `gal`, $\mathbb{T}$ (tower data giving fields $\mathbb{T}.F\ell$ with two finite integral $\mathbb{Q}^{\mathrm{alg}}$-embeddings $\mathbb{T}.\varphi(\ell,i)$ from $\bar{F}$), `galT`, $W$, `WT` be as in `ModuliTowerWitnessD`, let `tw` be such a witness, and let $\ell$ be a prime different from $q,q'$. Let $\pi_Y : Y \to \operatorname{Spec}\mathbb{Q}^{\mathrm{alg}}$ be integral, separated and smooth of relative dimension $1$, with a rule `ptT` making it a coarse moduli scheme (in the sense of `IsCoarseModuliT`, including the universal property) for pairs consisting of a fake elliptic curve of level $N$ and an extra level structure at $\ell$, and let $d_0, d_1 : Y \to X$ satisfy: the point of $Y$ attached to such a pair $u$, followed by $d_0$, is the point of $X$ attached to the underlying curve of $u$; and followed by $d_1$, it is the point attached to any $d$ admitting an $\ell$-level isogeny from $u$. Then there exist a curve model $\mathfrak{M}_\ell$ of $\mathbb{T}.F\ell$ over $\mathbb{Q}^{\mathrm{alg}}$ and an isomorphism $e_\ell : \mathfrak{M}_\ell.C \to Y$ with $e_\ell$ followed by $\pi_Y$ equal to $\mathfrak{M}_\ell.\mathrm{toBase}$, such that for every place $R$ of $\mathbb{T}.F\ell$ over $\mathbb{Q}^{\mathrm{alg}}$ and each $i \in \{0,1\}$, the $\mathbb{Q}^{\mathrm{alg}}$-point of $\mathfrak{M}_\ell.C$ corresponding to $R$, followed by $e_\ell$ and then $d_i$, equals the point of $\mathfrak{M}.C$ corresponding to the restriction of $R$ along $\mathbb{T}.\varphi(\ell,i)$, followed by $e_{\mathfrak{M}}$ and the first projection of the pullback.
--
--   This identifies the coarse moduli scheme of pairs (fake elliptic curve of level $N$, extra level structure at $\ell$) over $\mathbb{Q}^{\mathrm{alg}}$ with a smooth proper model of the tower field $\mathbb{T}.F\ell$, in such a way that the two degeneracy morphisms $d_0,d_1$ realise, on points, the two restriction maps of places along $\mathbb{T}.\varphi(\ell,0)$ and $\mathbb{T}.\varphi(\ell,1)$. It is the geometric input for the Hecke correspondence computation on the tower and for the Čerednik–Drinfeld reduction data built from the quaternionic moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_exists_curveModel_level_of_pt_pullback_of_two_mul_dvd_of_squarefree.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld NeronModelInfra
open CerednikDrinfeld.QM
open AlgebraicCurve

theorem CerednikDrinfeld.QM.ModuliTowerWitnessD.exists_curveModel_level_of_pt_pullback_of_two_mul_dvd_of_squarefree
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (hNsq : Squarefree N)
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
    (ℓ : HeckeTower.AwayPrime q q')

    (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) [IsIntegral Y] [IsSeparated πY]
    (hYsm : SmoothOfRelativeDimension 1 πY)
    (ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s πY)
    (hY : IsCoarseModuliT Λ N (ℓ.1 : ℕ) Y πY ptT)
    (d₀ d₁ : Y ⟶ X)
    (hd₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT S s u).1 ≫ d₀ = (pt S (s ≫ sbar) u.1).1)
    (hd₁ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S) (d : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) u d → (ptT S s u).1 ≫ d₁ = (pt S (s ≫ sbar) d).1) :
    ∃ (𝔐ℓ : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) (𝕋.F ℓ)) (eℓ : 𝔐ℓ.C ⟶ Y), IsIso eℓ ∧ eℓ ≫ πY = 𝔐ℓ.toBase ∧
      ∀ R : Place (AlgebraicClosure ℚ) (𝕋.F ℓ),
        (𝔐ℓ.pointEquivPlace.symm R).1 ≫ eℓ ≫ d₀ = (𝔐.pointEquivPlace.symm (R.restrictAlong (𝕋.φ (ℓ, 0)) (𝕋.integral (ℓ, 0)))).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar ∧
        (𝔐ℓ.pointEquivPlace.symm R).1 ≫ eℓ ≫ d₁ = (𝔐.pointEquivPlace.symm (R.restrictAlong (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 1)))).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar := by sorry
