-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_isLevelRestrict_and_isLevelIsogeny_rep_restrictAlong_of_coarse_of_two_mul_dvd
-- name    : CerednikDrinfeld.QM.isLevelRestrict_and_isLevelIsogeny_rep_restrictAlong_of_coarse_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/6cda39a3-850b-5bf2-a2be-401adf91e6fe
-- title:
--   Tower legs: forgetting the level and dividing by it
-- statement:
--   Fix natural numbers $N$ (nonzero), $q$, $q'$ prime with $q' \neq q$ and $q \nmid N$, $q' \nmid N$, and $D$ with $2Nqq' \mid D$; rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies $0<a$ or $0<b$ and is a division algebra over the completion at a height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ exactly when $q$ or $q'$ lies in $v$; and $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ a maximal order (a finitely generated $\mathbb{Z}$-submodule containing $1$, closed under multiplication, $\mathbb{Q}$-spanning, maximal among such). Further data: a field $\bar{F}$ over $\bar{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is a curve over it and essentially of finite type; a scheme $X$ over $\mathrm{Spec}\,\mathbb{Z}[1/D]$ with a geometric point $\bar{s}$ and a moduli point map $\mathrm{pt}$ for fake elliptic curves with $\Lambda$-action and level-$N$ structure, assumed isomorphism-invariant, compatible with base change, and bijective on isomorphism classes over algebraically closed fields; a proper smooth integral curve model $\mathfrak{M}$ of $\bar{F}$ over $\bar{\mathbb{Q}}$ identified by an isomorphism $e_{\mathfrak{M}}$ with the fibre $X \times_{\mathbb{Z}[1/D]} \bar{\mathbb{Q}}$ over the base map, together with a semilinear action $\mathrm{gal}$ of $\mathrm{Aut}(\bar{\mathbb{Q}}/\mathbb{Q})$ on $\bar{F}$ inducing the identity dictionary on base automorphisms and compatible with the point–place correspondence; a coarse moduli scheme $(\mathcal{X}, f, \mathrm{pt}_{\mathcal{X}})$ for fake elliptic curves over $\bar{\mathbb{Q}}$, isomorphic over $\bar{\mathbb{Q}}$ to that fibre compatibly with $\mathrm{pt}$; for each prime $\ell \neq q,q'$ a coarse moduli scheme $(\mathcal{Y}_\ell, g_\ell, \mathrm{pt}_T)$ for pairs consisting of such a curve with an extra level-$\ell$ subgroup, and morphisms $d_0, d_1 : \mathcal{Y}_\ell \to \mathcal{X}$ characterised on moduli points by sending the point of a pair $u$ to the point of its underlying curve, respectively to the point of any $d$ admitting an $\ell$-level isogeny from $u$; representatives $\mathrm{rep}\,P$ of the places of $\bar{F}$ and $\mathrm{repT}_\ell\,R$ of the places of the tower fields realising the corresponding moduli points; and tower data $\mathbb{T}$ with finite integral $\bar{\mathbb{Q}}$-algebra maps $\varphi_{\ell,i} : \bar{F} \to \mathbb{T}.F_\ell$ ($i \in \{0,1\}$), whose fields carry curve models $M_\ell$ isomorphic to $\mathcal{Y}_\ell$ over $\bar{\mathbb{Q}}$, such that restriction of places along $\varphi_{\ell,i}$ corresponds on points to $d_0$ for $i=0$ and to $d_1$ for $i=1$. The conclusion is the conjunction of two assertions, for every such $\ell$ and every place $P$ of $\mathbb{T}.F_\ell$: first, `IsLevelRestrict`, namely the underlying fake elliptic curve of $\mathrm{repT}_\ell\,P$ is isomorphic (compatibly with the group law, the $\Lambda$-action and the level-$N$ structure) to $\mathrm{rep}$ of the restriction of $P$ along $\varphi_{\ell,0}$; second, `IsLevelIsogeny` $\ell$, namely there are mutually inverse-up-to-$\ell$ $\Lambda$-equivariant morphisms between $\mathrm{repT}_\ell\,P$ and $\mathrm{rep}$ of the restriction of $P$ along $\varphi_{\ell,1}$, whose composites in both orders are the action of $\ell$, the first having kernel exactly the extra level-$\ell$ subgroup and carrying the level-$N$ structure into the level-$N$ structure.
--
--   This is the statement that the two degeneracy legs of the constructed Hecke tower over a Shimura curve of quaternionic type read on representatives as forgetting the extra level-$\ell$ subgroup and as dividing by it. It supplies the two level-compatibility clauses of the moduli-tower witness used in [`CerednikDrinfeld.QM.exists_moduliTowerWitness_of_two_mul_dvd_of_neZero_of_squarefree`](thm.html#CerednikDrinfeld.QM.exists_moduliTowerWitness_of_two_mul_dvd_of_neZero_of_squarefree).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_isLevelRestrict_and_isLevelIsogeny_rep_restrictAlong_of_coarse_of_two_mul_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.isLevelRestrict_and_isLevelIsogeny_rep_restrictAlong_of_coarse_of_two_mul_dvd
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
    (∀ (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    FakeEllipticCurve.IsLevelRestrict (repT ℓ P) (rep (P.restrictAlong (𝕋.φ (ℓ, 0)) (𝕋.integral (ℓ, 0))))) ∧
    (∀ (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) (repT ℓ P) (rep (P.restrictAlong (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 1))))) := by sorry
