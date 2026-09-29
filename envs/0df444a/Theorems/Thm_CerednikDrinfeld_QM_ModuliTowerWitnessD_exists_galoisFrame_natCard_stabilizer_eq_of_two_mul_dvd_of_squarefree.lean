-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_exists_galoisFrame_natCard_stabilizer_eq_of_two_mul_dvd_of_squarefree
-- name    : CerednikDrinfeld.QM.ModuliTowerWitnessD.exists_galoisFrame_natCard_stabilizer_eq_of_two_mul_dvd_of_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/aef16c91-bb87-5ce9-8f32-f95691ec79de
-- title:
--   Decomposition-group count along the level-forgetting leg of the tower
-- statement:
--   Fix naturals $N \neq 0$ and primes $q \neq q'$ with $q \nmid N$, $q' \nmid N$ and $N$ squarefree, and $D$ with $2Nqq' \mid D$; let $a,b \in \mathbb{Q}$ satisfy `IsIndefiniteRamifiedExactlyAt`, i.e. $0 < a$ or $0 < b$ and, for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $q$ or $q'$ lies in $v$; let $\Lambda$ be a maximal order in $\mathbb{H}[\mathbb{Q},a,b]$ (an order maximal among orders). Let $Fbar$ be a function field of a curve over $\overline{\mathbb{Q}}$ in the sense of `IsCurveOver` and essentially of finite type, and let $(X,\pi_X)$ over $\operatorname{Spec} \mathbb{Z}[1/D]$ together with a point map $pt$ on fake elliptic curves $(\Lambda,N)$ be a coarse moduli datum: $pt$ is constant on isomorphism classes, compatible with base change along ring maps and pullback of fake elliptic curves, and bijective on isomorphism classes over algebraically closed fields. Further data: a $\overline{\mathbb{Q}}$-point $sbar$ of the base; a curve model $\mathfrak{M}$ of $Fbar$ with an isomorphism $e\mathfrak{M} : \mathfrak{M}.C \to X \times_{\mathbb{Z}[1/D]} \overline{\mathbb{Q}}$ over $\overline{\mathbb{Q}}$; semilinear Galois actions $gal$, $galT$ and semilinear involutive data $W$, $WT$; tower data $\mathbb{T}$ of fields $\mathbb{T}.F_\ell$ over $Fbar$, finite and integral along the structural maps $\mathbb{T}.\varphi$; and a witness $tw$ of `ModuliTowerWitnessD` for all of these. Fix a prime $\ell \notin \{q,q'\}$, an integral scheme $Y$ with separated, smooth of relative dimension one structural map $\pi_Y$ to $\operatorname{Spec} \overline{\mathbb{Q}}$ carrying a point map $ptT$ on pairs (fake elliptic curve, extra level of rank $\ell^2$) which makes $Y$ a coarse moduli space in the sense of `IsCoarseModuliT`, a morphism $d_0 : Y \to X$ with $(ptT\,u) \text{ followed by } d_0 = pt\,(u.1)$ for all $u$, and a curve model $\mathfrak{M}_\ell$ of $\mathbb{T}.F_\ell$ with an isomorphism $e_\ell : \mathfrak{M}_\ell.C \to Y$ over $\overline{\mathbb{Q}}$ such that on $\overline{\mathbb{Q}}$-points $e_\ell$ followed by $d_0$ induces restriction of places along $\mathbb{T}.\varphi(\ell,0)$. Finally fix a place $R$ of $\mathbb{T}.F_\ell$ over $\overline{\mathbb{Q}}$, a fake elliptic curve $E$ over $\overline{\mathbb{Q}}$ whose moduli point is the point of $X$ attached to the restriction of $R$ along $\mathbb{T}.\varphi(\ell,0)$, and a family $K_0,\dots,K_{n-1}$ of extra $\ell$-level structures on $E$ which is irredundant and exhaustive for the relation 'the same points factor through $levK$'. The conclusion: there is a field $M_f$, an extension of $Fbar$ and of $\mathbb{T}.F_\ell$ compatibly over $\overline{\mathbb{Q}}$, finite over each and Galois over $Fbar$, and a place $c$ of $M_f$ over $\overline{\mathbb{Q}}$, such that the embedding of $Fbar$ into $M_f$ equals $\mathbb{T}.\varphi(\ell,0)$ followed by that of $\mathbb{T}.F_\ell$, the restriction of $c$ to $\mathbb{T}.F_\ell$ is $R$, and the number of $\sigma \in \mathrm{Gal}(M_f/Fbar)$ fixing $c$ (acting on places through `SemilinearAut.ofAlgAut`) equals the number of indices $i$ with $ptT(E,K_i)$ equal to the $\overline{\mathbb{Q}}$-point of $Y$ attached to $R$ by $\mathfrak{M}_\ell$ and $e_\ell$, multiplied by the number of $\sigma \in \mathrm{Gal}(M_f/\mathbb{T}.F_\ell)$ fixing $c$.
--
--   This is the moduli-theoretic half of the computation of the ramification of the level-forgetting map $d_0$ from the $\ell$-layer of the Hecke tower down to the base Shimura curve at a point classifying a pair $(E,K)$: the decomposition group upstairs is the orbit count of extra level structures on $E$ times the decomposition group of the chosen Galois frame over $\mathbb{T}.F_\ell$. It is used by [`CerednikDrinfeld.QM.ModuliTowerWitnessD.ramificationIndexAlong_eq_card_of_pt_pullback_of_two_mul_dvd_of_squarefree`](thm.html#CerednikDrinfeld.QM.ModuliTowerWitnessD.ramificationIndexAlong_eq_card_of_pt_pullback_of_two_mul_dvd_of_squarefree), which combines it with Hilbert ramification theory and the triviality of residue degrees over an algebraically closed base field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_exists_galoisFrame_natCard_stabilizer_eq_of_two_mul_dvd_of_squarefree.lean

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

theorem CerednikDrinfeld.QM.ModuliTowerWitnessD.exists_galoisFrame_natCard_stabilizer_eq_of_two_mul_dvd_of_squarefree
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
    ∃ (Mf : Type) (_ : Field Mf) (_ : Algebra (AlgebraicClosure ℚ) Mf) (_ : Algebra Fbar Mf) (_ : Algebra (𝕋.F ℓ) Mf)
      (_ : IsScalarTower (AlgebraicClosure ℚ) Fbar Mf) (_ : IsScalarTower (AlgebraicClosure ℚ) (𝕋.F ℓ) Mf)
      (_ : FiniteDimensional Fbar Mf) (_ : FiniteDimensional (𝕋.F ℓ) Mf) (_ : IsGalois Fbar Mf)
      (c : Place (AlgebraicClosure ℚ) Mf),
      (∀ x : Fbar, algebraMap Fbar Mf x = algebraMap (𝕋.F ℓ) Mf (𝕋.φ (ℓ, 0) x)) ∧
      c.restrict (𝕋.F ℓ) = R ∧
      Nat.card {σ : Mf ≃ₐ[Fbar] Mf // SemilinearAut.ofAlgAut (σ.restrictScalars (AlgebraicClosure ℚ)) • c = c} =
        Nat.card {i : Fin n //
          (ptT _ (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) (⟨E, K i⟩ : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) (AlgebraicClosure ℚ))).1 =
            (𝔐ℓ.pointEquivPlace.symm R).1 ≫ eℓ} *
        Nat.card {σ : Mf ≃ₐ[𝕋.F ℓ] Mf // SemilinearAut.ofAlgAut (σ.restrictScalars (AlgebraicClosure ℚ)) • c = c} := by sorry
