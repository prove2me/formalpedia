-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_WT_of_coarse_of_two_mul_dvd
-- name    : CerednikDrinfeld.QM.exists_WT_of_coarse_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/4e6c32ba-ad07-51c5-b49d-83b10b3d5db3
-- title:
--   Atkin–Lehner involutions on the tower's upper function fields
-- statement:
--   Fix a positive integer $N$ and primes $q\neq q'$ with $q\nmid N$ and $q'\nmid N$, and an integer $D$ divisible by $2Nqq'$. Let $a,b\in\mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, that is $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $q$ or $q'$ lies in $v$; let $\Lambda$ be a maximal order in it. The data are: a field $\bar F$ that is a curve over $\overline{\mathbb{Q}}$ of essentially finite type; a scheme $X$ over $\operatorname{Spec}\mathbb{Z}[1/D]$ together with a geometric point $\bar s$ of the base and a moduli assignment `pt` sending a fake elliptic curve of level $N$ for $\Lambda$ over a ring $S$ to a point of $X$ over $S$, assumed invariant under isomorphism, compatible with pullback, and bijective on isomorphism classes over algebraically closed fields; a curve model $\mathfrak{M}$ of $\bar F$ over $\overline{\mathbb{Q}}$ with an isomorphism $e_{\mathfrak M}$ onto the fibre $X\times_{\bar s}\operatorname{Spec}\overline{\mathbb{Q}}$ compatible with the structure morphisms; a semilinear action `gal` of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $\bar F$ inducing the given automorphism on $\overline{\mathbb{Q}}$ and acting on places through the Galois twist of points; a coarse moduli scheme $(\mathcal{X},f,\mathrm{pt}_{\mathcal X})$ for fake elliptic curves of level $N$ over $\overline{\mathbb{Q}}$ in the sense of `IsCoarseModuli`, identified isomorphically with that same fibre compatibly with `pt`; for each prime $\ell\notin\{q,q'\}$ a coarse moduli scheme $(\mathcal{Y}_\ell,g_\ell,\mathrm{pt}_{T,\ell})$ for fake elliptic curves of level $N$ with an extra $\ell$-level structure, together with two morphisms $d_0,d_1:\mathcal{Y}_\ell\to\mathcal{X}$ characterised on moduli points by forgetting the extra structure, respectively by passing to any target of an $\ell$-level isogeny; representatives $\mathrm{rep}$ of the places of $\bar F$ and $\mathrm{repT}_\ell$ of the places of the upper fields by objects over $\overline{\mathbb{Q}}$ whose moduli points are the corresponding points; and a tower datum $\mathbb{T}$ over $\bar F$ with curve models $M_\ell$ of its fields $\mathbb{T}.F_\ell$, isomorphisms $e_\ell:M_\ell.C\to\mathcal{Y}_\ell$ over $\overline{\mathbb{Q}}$, such that restriction of places along $\mathbb{T}.\varphi_{(\ell,i)}$ corresponds on points to $e_\ell$ followed by $d_0$ for $i=0$ and by $d_1$ for $i=1$. The conclusion asserts the existence, for every such $\ell$ and every $i\in\{0,1\}$, of a semilinear automorphism $WT_{\ell,i}$ of $\mathbb{T}.F_\ell$ over $\overline{\mathbb{Q}}$ whose base automorphism is the identity, hence $\overline{\mathbb{Q}}$-linear, such that for every place $P$ of $\mathbb{T}.F_\ell$ the pair $\mathrm{repT}_\ell(WT_{\ell,0}\cdot P)$ is an Atkin–Lehner quotient at $q$ of $\mathrm{repT}_\ell(P)$, and $\mathrm{repT}_\ell(WT_{\ell,1}\cdot P)$ one at $q'$, in the sense of `FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient`: there are mutually inverse-up-to-$r$ morphisms between the two abelian schemes, respecting the group laws and the $\Lambda$-actions, whose composites are the action of $r$ ($r=q$ or $q'$), with the prescribed kernel condition and preservation of both the $N$- and the $\ell$-level structures.
--
--   This is the construction of the two Atkin–Lehner operators at the ramified primes $q$ and $q'$ on the upper layers of the Hecke tower attached to a quaternionic (fake elliptic curve) moduli problem: they appear as $\overline{\mathbb{Q}}$-linear automorphisms of the function fields $\mathbb{T}.F_\ell$ acting on places exactly as the Atkin–Lehner quotient construction acts on the representing pairs. It feeds the assembly of the full tower witness in [`CerednikDrinfeld.QM.exists_moduliTowerWitness_of_two_mul_dvd_of_neZero_of_squarefree`](thm.html#CerednikDrinfeld.QM.exists_moduliTowerWitness_of_two_mul_dvd_of_neZero_of_squarefree), where these involutions supply the Atkin–Lehner structure needed on the Čerednik–Drinfeld side of the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_WT_of_coarse_of_two_mul_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.exists_WT_of_coarse_of_two_mul_dvd
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
    ∃ WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ),
      (∀ (ℓ : HeckeTower.AwayPrime q q') (i : Fin 2) (c : AlgebraicClosure ℚ), SemilinearAut.baseAut (WT ℓ i) c = c) ∧
      (∀ (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient q (repT ℓ P) (repT ℓ (WT ℓ 0 • P))) ∧
      (∀ (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient q' (repT ℓ P) (repT ℓ (WT ℓ 1 • P))) := by sorry
