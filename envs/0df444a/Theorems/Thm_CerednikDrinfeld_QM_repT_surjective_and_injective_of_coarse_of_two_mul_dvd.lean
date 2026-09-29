-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_repT_surjective_and_injective_of_coarse_of_two_mul_dvd
-- name    : CerednikDrinfeld.QM.repT_surjective_and_injective_of_coarse_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/f05ebe41-ded6-5d0e-a3be-e7c0d70b6fae
-- title:
--   Tower representatives meet every level structure exactly once
-- statement:
--   Fix natural numbers $N, q, q'$ with $q, q'$ prime, $q \nmid N$, $q' \nmid N$ and $q' \neq q$, and $D$ with $2Nqq' \mid D$; the base ring throughout is the localisation $\mathbb{Z}[1/D]$. Let $a, b \in \mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q}, a, b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and a height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ has the property that every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $q \in v$ or $q' \in v$; and let $\Lambda$ be a maximal order in it (a finitely generated $\mathbb{Z}$-submodule containing $1$, closed under multiplication, spanning over $\mathbb{Q}$, and maximal among such). Let $\bar{F}$ be a curve function field over $\overline{\mathbb{Q}}$, essentially of finite type. The data are grouped as follows: a scheme $X$ over $\mathbb{Z}[1/D]$ with a moduli map `pt` on `FakeEllipticCurve Λ N S`-objects satisfying the four coarse-moduli axioms (invariance under isomorphism, compatibility with pullback, and bijectivity up to isomorphism on geometric points) and a geometric base point `sbar`; a curve model $\mathfrak{M}$ of $\bar{F}$ with an isomorphism $e_{\mathfrak M}$ onto the pullback of $X$ along `sbar` over the base, together with a Galois action by semilinear automorphisms inducing the given automorphism on $\overline{\mathbb{Q}}$ and compatible with `pt` on points; a coarse moduli space $(\mathcal{X}, f, \mathrm{pt}_{\mathcal X})$ over $\overline{\mathbb{Q}}$ in the sense of `IsCoarseModuli`, isomorphic to that pullback and compatible with `pt`; for each prime $\ell \neq q, q'$ a coarse moduli space $(\mathcal{Y}_\ell, g_\ell, \mathrm{pt}_{T,\ell})$ for `FakeEllipticCurve.WithExtraLevel Λ N ℓ` in the sense of `IsCoarseModuliT`, with degeneracy morphisms $d_0, d_1 : \mathcal{Y}_\ell \to \mathcal{X}$ characterised on moduli points by forgetting the extra level and by passing along a level-$\ell$ isogeny; representatives `rep` of the places of $\bar F$ whose moduli points are the corresponding points of $\mathfrak{M}$; and a tower datum $\mathbb{T}$ for $q, q'$ over $\bar F$ with curve models $M_\ell$ of $\mathbb{T}.F\,\ell$ isomorphic to $\mathcal{Y}_\ell$ over $\overline{\mathbb{Q}}$, such that restriction of places along $\mathbb{T}.\varphi(\ell, i)$ corresponds on points to $d_0$ for $i = 0$ and to $d_1$ otherwise, together with representatives $\mathrm{repT}_\ell R \in$ `FakeEllipticCurve.WithExtraLevel Λ N ℓ` $\overline{\mathbb{Q}}$ of the places $R$ of $\mathbb{T}.F\,\ell$ whose moduli points are the points of $M_\ell$ attached to $R$. The conclusion is the conjunction of two assertions: for every $\ell$ and every object $u$ of `FakeEllipticCurve.WithExtraLevel Λ N ℓ` over $\overline{\mathbb{Q}}$ there is a place $P$ of $\mathbb{T}.F\,\ell$ with $\mathrm{repT}_\ell P \cong u$; and for all places $P, Q$ of $\mathbb{T}.F\,\ell$, an isomorphism $\mathrm{repT}_\ell P \cong \mathrm{repT}_\ell Q$ forces $P = Q$.
--
--   This supplies the surjectivity and injectivity properties of the upper-level representatives in a moduli tower of fake elliptic curves with auxiliary level-$\ell$ structure, in the version where the integral base is $\mathbb{Z}[1/D]$ for any $D$ divisible by $2Nqq'$. It is used in the construction of a moduli tower witness by [`CerednikDrinfeld.QM.exists_moduliTowerWitness_of_two_mul_dvd_of_neZero_of_squarefree`](thm.html#CerednikDrinfeld.QM.exists_moduliTowerWitness_of_two_mul_dvd_of_neZero_of_squarefree), where places of the upper function fields are to be identified with isomorphism classes of level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_repT_surjective_and_injective_of_coarse_of_two_mul_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.repT_surjective_and_injective_of_coarse_of_two_mul_dvd
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
    (hgal_base : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), SemilinearAut.baseAut (gal σ) = (σ : (AlgebraicClosure ℚ) ≃+* (AlgebraicClosure ℚ)))

    (hgal_pt : ∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (P : Place (AlgebraicClosure ℚ) Fbar),
      (𝔐.pointEquivPlace.symm (gal σ • P)).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar =
        Spec.map (CommRingCat.ofHom (σ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫
          ((𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar))
    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
    (pt𝒳 : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))),
      FakeEllipticCurve Λ N S → SchemeHomOver s f)
    (hco : IsCoarseModuli Λ N 𝒳 f pt𝒳)
    (g𝒳 : 𝒳 ⟶ CategoryTheory.Limits.pullback πX sbar) [IsIso g𝒳]
    (hg𝒳 : g𝒳 ≫ CategoryTheory.Limits.pullback.snd πX sbar = f)
    (hg𝒳pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (E : FakeEllipticCurve Λ N S),
      (pt𝒳 S s E).1 ≫ g𝒳 ≫ CategoryTheory.Limits.pullback.fst πX sbar = (pt S (s ≫ sbar) E).1)
    (𝒴 : HeckeTower.AwayPrime q q' → Scheme.{0})
    (g : ∀ ℓ, 𝒴 ℓ ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
    (ptT : ∀ (ℓ : HeckeTower.AwayPrime q q') (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (g ℓ))
    (hcoT : ∀ ℓ, IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴 ℓ) (g ℓ) (ptT ℓ))
    (d₀ d₁ : ∀ ℓ, 𝒴 ℓ ⟶ 𝒳)
    (hd₀ : ∀ (ℓ : HeckeTower.AwayPrime q q') (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT ℓ S s u).1 ≫ d₀ ℓ = (pt𝒳 S s u.1).1)
    (hd₁ : ∀ (ℓ : HeckeTower.AwayPrime q q') (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S) (d : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) u d → (ptT ℓ S s u).1 ≫ d₁ ℓ = (pt𝒳 S s d).1)
    (rep : Place (AlgebraicClosure ℚ) Fbar → FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (pt_rep : ∀ P : Place (AlgebraicClosure ℚ) Fbar,
      (pt _ sbar (rep P)).1 = (𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar)
    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (Mℓ : ∀ ℓ : HeckeTower.AwayPrime q q', AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (eℓ : ∀ ℓ : HeckeTower.AwayPrime q q', (Mℓ ℓ).C ⟶ 𝒴 ℓ) (heℓiso : ∀ ℓ, IsIso (eℓ ℓ))
    (heℓ : ∀ ℓ, eℓ ℓ ≫ g ℓ = (Mℓ ℓ).toBase)

    (hφpt : ∀ (ℓ : HeckeTower.AwayPrime q q') (i : Fin 2) (R : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
      (𝔐.pointEquivPlace.symm (R.restrictAlong (𝕋.φ (ℓ, i)) (𝕋.integral (ℓ, i)))).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar =
        ((Mℓ ℓ).pointEquivPlace.symm R).1 ≫ eℓ ℓ ≫ (if i = 0 then d₀ ℓ else d₁ ℓ) ≫ g𝒳 ≫ CategoryTheory.Limits.pullback.fst πX sbar)
    (repT : ∀ ℓ : HeckeTower.AwayPrime q q',
      Place (AlgebraicClosure ℚ) (𝕋.F ℓ) → FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) (AlgebraicClosure ℚ))
    (ptT_repT : ∀ (ℓ : HeckeTower.AwayPrime q q') (R : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
      (ptT ℓ _ (𝟙 _) (repT ℓ R)).1 = ((Mℓ ℓ).pointEquivPlace.symm R).1 ≫ eℓ ℓ)
 :
    (∀ (ℓ : HeckeTower.AwayPrime q q') (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) (AlgebraicClosure ℚ)),
    ∃ P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ), FakeEllipticCurve.WithExtraLevel.Iso (repT ℓ P) u) ∧
    (∀ (ℓ : HeckeTower.AwayPrime q q') (P Q : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    FakeEllipticCurve.WithExtraLevel.Iso (repT ℓ P) (repT ℓ Q) → P = Q) := by sorry
