-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_isPullback_rep_gal_smul_of_two_mul_dvd
-- name    : CerednikDrinfeld.QM.exists_isPullback_rep_gal_smul_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/54470314-de9d-5786-9066-6213b27ef876
-- title:
--   Galois moves place representatives by base change along σ
-- statement:
--   Fix a nonzero natural number $N$ and primes $q \neq q'$, neither dividing $N$, and a natural number $D$ divisible by $2Nqq'$; the base is $R =$ the localisation of $\mathbb{Z}$ away from $D$. Let $\mathbb{H}[\mathbb{Q},a,b]$ satisfy `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra precisely when $q$ or $q'$ lies in $v$; let $\Lambda$ be a maximal order, that is a finitely generated $\mathbb{Z}$-submodule containing $1$, closed under multiplication and $\mathbb{Q}$-spanning, maximal among such. Let $\bar{F}$ be a field extension of $\bar{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is a curve over it (principal divisors exist, residue fields of places are finite-dimensional, $\Omega_{\bar F/\bar{\mathbb{Q}}}$ free of rank one) and essentially of finite type. The data consist of: a scheme $X$ with a morphism $\pi_X$ to $\operatorname{Spec} R$; a $\bar{\mathbb{Q}}$-point $\bar{s}$ of $\operatorname{Spec} R$; an assignment `pt` sending a fake elliptic curve $E$ over an $R$-scheme base $s : \operatorname{Spec} S \to \operatorname{Spec} R$ (an abelian scheme over $S$ with commutative relative group law, two-dimensional fibres, $\Lambda$-action with the trace condition, and level-$N$ datum) to a morphism $\operatorname{Spec} S \to X$ over $s$, subject to invariance under `FakeEllipticCurve.Iso`, compatibility with base change along ring maps $\varphi$ (if $E'$ is a `FakeEllipticCurve.IsPullback` of $E$ along $\varphi$ then its $X$-point is $\operatorname{Spec}\varphi$ followed by that of $E$), and surjectivity and injectivity up to isomorphism on points with values in algebraically closed fields; a `CurveModel` $\mathfrak{M}$ of $\bar F/\bar{\mathbb{Q}}$ with an isomorphism $e_{\mathfrak M}$ onto the fibre product of $\pi_X$ and $\bar s$ compatible with the structure morphisms; a homomorphism `gal` from $\operatorname{Aut}_{\mathbb{Q}}(\bar{\mathbb{Q}})$ to the semilinear automorphisms of $\bar F$ over $\bar{\mathbb{Q}}$ whose base component is $\sigma$ itself; the hypothesis that the $X$-point attached through $\mathfrak{M}$ to $\mathrm{gal}(\sigma) \cdot P$ is $\operatorname{Spec}\sigma$ followed by the $X$-point attached to $P$; and representatives $\mathrm{rep}\,P$, fake elliptic curves over $\bar{\mathbb{Q}}$ whose $X$-point is the one attached to the place $P$. The conclusion is that for every $\sigma$ and every place $P$ of $\bar F$ over $\bar{\mathbb{Q}}$ there is a fake elliptic curve $E$ over $\bar{\mathbb{Q}}$ which is a base change of $\mathrm{rep}\,P$ along $\sigma$ (a cartesian square compatible with the group laws, the $\Lambda$-actions and the level data) and which is isomorphic to $\mathrm{rep}(\mathrm{gal}(\sigma)\cdot P)$.
--
--   This is the Galois-equivariance clause for the chosen representatives in the moduli description of the Shimura curve attached to the indefinite quaternion algebra ramified exactly at $q$ and $q'$: conjugating a fake elliptic curve by $\sigma$ realises the action of $\sigma$ on places of the function field. It is used in the assembly of the moduli tower witness, [`CerednikDrinfeld.QM.exists_moduliTowerWitness_of_two_mul_dvd_of_neZero_of_squarefree`](thm.html#CerednikDrinfeld.QM.exists_moduliTowerWitness_of_two_mul_dvd_of_neZero_of_squarefree).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_isPullback_rep_gal_smul_of_two_mul_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.exists_isPullback_rep_gal_smul_of_two_mul_dvd
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
    (rep : Place (AlgebraicClosure ℚ) Fbar → FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (pt_rep : ∀ P : Place (AlgebraicClosure ℚ) Fbar,
      (pt _ sbar (rep P)).1 = (𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar) :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (P : Place (AlgebraicClosure ℚ) Fbar),
    ∃ E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ),
      FakeEllipticCurve.IsPullback (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (rep P) E ∧
        FakeEllipticCurve.Iso E (rep (gal σ • P)) := by sorry
