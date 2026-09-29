-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_ramificationIndexAlong_eq_card_of_pt_pullback_of_two_mul_dvd_of_squarefree
-- name    : CerednikDrinfeld.QM.ModuliTowerWitnessD.ramificationIndexAlong_eq_card_of_pt_pullback_of_two_mul_dvd_of_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/0ba55a39-9bcc-5881-b9b1-2ed3bbe304f4
-- title:
--   Ramification along the level-forgetting leg counts extra levels
-- statement:
--   Let $N,q,q'$ be natural numbers with $N \neq 0$, $q$ and $q'$ prime, $q \nmid N$, $q' \nmid N$, $q' \neq q$ and $N$ squarefree, and let $D$ be a natural number divisible by $2Nqq'$. Let $a,b \in \mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0 < a$ or $0 < b$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit precisely when $v$ contains $q$ or $q'$; let $\Lambda$ be a maximal order in $\mathbb{H}[\mathbb{Q},a,b]$, that is, an order (containing $1$, closed under multiplication, spanning over $\mathbb{Q}$, finitely generated) maximal among the orders containing it. Let $Fbar$ be a field extension of $\overline{\mathbb{Q}}$ which is a curve over $\overline{\mathbb{Q}}$ (principal divisors exist, residue fields of places are finite-dimensional, $\Omega_{Fbar/\overline{\mathbb{Q}}}$ is free of rank one) and essentially of finite type. Let $\pi_X : X \to \operatorname{Spec} \mathbb{Z}[1/D]$ be a scheme over the localisation of $\mathbb{Z}$ away from $D$, $\overline{s}$ a $\overline{\mathbb{Q}}$-point of that base, and $\mathrm{pt}$ an assignment sending each ring $S$, each $S$-point $s$ of the base and each fake elliptic curve with $\Lambda$-action and level-$N$ structure over $S$ to a morphism $\operatorname{Spec} S \to X$ over $s$, subject to the four moduli laws: invariance under isomorphism, compatibility with base change along ring maps and pullback of curves, and surjectivity and injectivity-up-to-isomorphism on points with values in algebraically closed fields. Let $\mathfrak{M}$ be a curve model of $Fbar$ over $\overline{\mathbb{Q}}$ together with an isomorphism $e_{\mathfrak M} : \mathfrak{M}.C \to X \times_{\operatorname{Spec}\mathbb{Z}[1/D]} \operatorname{Spec}\overline{\mathbb{Q}}$ compatible with the structure morphisms, let $gal$, $W$, $\mathbb{T}$ (a Hecke tower of curve fields $\mathbb{T}.F_\ell$ over $Fbar$, indexed by primes $\ell \neq q,q'$, with finite integral $\overline{\mathbb{Q}}$-algebra maps $\mathbb{T}.\varphi$), $galT$ and $WT$ be as in the tower data, and let $tw$ be a `ModuliTowerWitnessD` for these. Fix a prime $\ell \neq q,q'$, an integral separated scheme $\pi_Y : Y \to \operatorname{Spec}\overline{\mathbb{Q}}$ smooth of relative dimension one with a point assignment $\mathrm{pt}_T$ making it a coarse moduli scheme for pairs consisting of such a curve together with an extra level of order $\ell$, a morphism $d_0 : Y \to X$ with $\mathrm{pt}_T(S,s,u)$ followed by $d_0$ equal to $\mathrm{pt}(S, s \circ \overline{s}, u_1)$, a curve model $\mathfrak{M}_\ell$ of $\mathbb{T}.F_\ell$ with an isomorphism $e_\ell : \mathfrak{M}_\ell.C \to Y$ over $\overline{\mathbb{Q}}$, and the compatibility that for every place $R$ of $\mathbb{T}.F_\ell$ the point of $R$ followed by $e_\ell$ and $d_0$ agrees with the point of the restriction of $R$ along $\mathbb{T}.\varphi(\ell,0)$ followed by $e_{\mathfrak M}$ and the first projection. Finally let $R$ be a place of $\mathbb{T}.F_\ell$, let $E$ be a fake elliptic curve over $\overline{\mathbb{Q}}$ whose moduli point is the point attached to the restriction of $R$ along $\mathbb{T}.\varphi(\ell,0)$, and let $K_0,\dots,K_{n-1}$ be extra levels of order $\ell$ on $E$ that are pairwise distinct and exhaustive, distinctness and exhaustiveness both being measured by which $\overline{\mathbb{Q}}$-points of $E$ factor through the level subscheme. Then the ramification index of $R$ along $\mathbb{T}.\varphi(\ell,0)$, i.e. the least positive $m$ of the form $\mathrm{ord}_R(\mathbb{T}.\varphi(\ell,0)(f))$ for some nonzero $f \in Fbar$, equals the number of indices $i$ for which the moduli point of the pair $(E,K_i)$ over the identity base point coincides with the point of $R$ followed by $e_\ell$.
--
--   This is the ramification computation for the first leg of the Hecke correspondence on the tower of fake-elliptic-curve moduli curves: the local degree of the level-forgetting map at a place is the number of extra $\ell$-levels on the corresponding fake elliptic curve that give the same moduli point, i.e. the size of the orbit of the level under the automorphisms of the curve. It is used in the derivation of the formula expressing the pullback of a single place under the correspondence as a sum over the points above it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_ramificationIndexAlong_eq_card_of_pt_pullback_of_two_mul_dvd_of_squarefree.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
open AlgebraicCurve

theorem CerednikDrinfeld.QM.ModuliTowerWitnessD.ramificationIndexAlong_eq_card_of_pt_pullback_of_two_mul_dvd_of_squarefree
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hNsq : Squarefree N)
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
    (d₀ : Y ⟶ X)
    (hd₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT S s u).1 ≫ d₀ = (pt S (s ≫ sbar) u.1).1)
    (𝔐ℓ : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) (𝕋.F ℓ)) (eℓ : 𝔐ℓ.C ⟶ Y) [IsIso eℓ] (heℓ : eℓ ≫ πY = 𝔐ℓ.toBase)
    (hcompat₀ : ∀ R : Place (AlgebraicClosure ℚ) (𝕋.F ℓ),
      (𝔐ℓ.pointEquivPlace.symm R).1 ≫ eℓ ≫ d₀ = (𝔐.pointEquivPlace.symm (R.restrictAlong (𝕋.φ (ℓ, 0)) (𝕋.integral (ℓ, 0)))).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar)

    (R : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)) (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (hE : (pt _ sbar E).1 = (𝔐.pointEquivPlace.symm (R.restrictAlong (𝕋.φ (ℓ, 0)) (𝕋.integral (ℓ, 0)))).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar)
    (n : ℕ) (K : Fin n → E.ExtraLevel (ℓ.1 : ℕ))
    (hKdist : ∀ i j : Fin n,
      (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f,
        FactorsThrough (K i).levK x ↔ FactorsThrough (K j).levK x) → i = j)
    (hKexh : ∀ K' : E.ExtraLevel (ℓ.1 : ℕ), ∃ i : Fin n,
      ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f,
        FactorsThrough K'.levK x ↔ FactorsThrough (K i).levK x) :
    Place.ramificationIndexAlong (𝕋.φ (ℓ, 0)) R =
      Nat.card {i : Fin n //
        (ptT _ (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) (⟨E, K i⟩ : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) (AlgebraicClosure ℚ))).1 =
          (𝔐ℓ.pointEquivPlace.symm R).1 ≫ eℓ} := by sorry
