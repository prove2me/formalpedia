-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_ModuliTowerWitness_mem_support_correspondence_single_iff_heckeNeighbour_of_two_mul_dvd
-- name    : CerednikDrinfeld.QM.ModuliTowerWitness.mem_support_correspondence_single_iff_heckeNeighbour_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/776fb2e6-6a54-542f-8596-d12269df766b
-- title:
--   Hecke correspondence support as ℓ-Hecke neighbours of fake elliptic curves
-- statement:
--   Fix a level $N \ne 0$ and primes $q, q'$ with $q' \ne q$, neither dividing $N$, and a nonzero integer $D$ divisible by $2Nqq'$. Let $\mathbb{H}[\mathbb{Q},a,b]$ be a quaternion algebra satisfying `IsIndefiniteRamifiedExactlyAt a b q q'` (namely $0 < a$ or $0 < b$, and for each finite place $v$ of $\mathbb{Q}$ the completion is a division algebra exactly when $v$ lies over $q$ or $q'$), and let $\Lambda$ be a maximal order in it, i.e. an order maximal among orders containing it. Let $X$ be an integral scheme with a smooth, proper morphism $\pi_X$ of relative dimension one to $\operatorname{Spec}$ of the localisation of $\mathbb{Z}$ away from $D$, together with an assignment $\mathrm{pt}$ sending a fake elliptic curve over $S$ (an abelian scheme of relative dimension two with commutative relative group law, $\Lambda$-action with the trace condition, and level-$N$ structure, in the sense of `FakeEllipticCurve`) to a point of $X$ over the given base morphism; $\mathrm{pt}$ is assumed to be invariant under `FakeEllipticCurve.Iso`, compatible with base change along ring maps and pullbacks of fake elliptic curves, and surjective and injective up to isomorphism on algebraically closed fields, with all geometric fibres of $\pi_X$ integral. Let $\bar{s}$ be a geometric base point over $\overline{\mathbb{Q}}$ compatible with the structure maps from $\mathbb{Z}$, let $\bar F$ be a curve function field over $\overline{\mathbb{Q}}$ carrying a semilinear Galois action `gal`, let $\mathfrak{M}$ be a `CurveModel` of $\bar F$ with an isomorphism $e_{\mathfrak{M}}$ from $\mathfrak{M}.C$ to the fibre of $\pi_X$ at $\bar s$ over the base, let $\mathbb{T}$ be a tower `HeckeTower.TowerData q q'` of finite integral extensions of $\bar F$ indexed by primes away from $q,q'$ with two degeneracy maps $\varphi_{\ell,0},\varphi_{\ell,1}$ at each $\ell$, with semilinear Galois actions `galT` and involutions `W`, `WT`, and let `tw` be a witness of type `ModuliTowerWitnessD` relating the tower to the moduli interpretation. Then for every prime $\ell$ away from $q,q'$ with $\ell \nmid N$ and all places $P, Q$ of $\bar F$ over $\overline{\mathbb{Q}}$: $Q$ lies in the support of the push–pull divisor $(\varphi_{\ell,1})_*(\varphi_{\ell,0})^*(\mathrm{single}\,P\,1)$ if and only if there exist fake elliptic curves $E, E'$ over $\overline{\mathbb{Q}}$ of level $N$ whose images under $\mathrm{pt}$ at $\bar s$ are the $\overline{\mathbb{Q}}$-points of $X$ corresponding to $P$ and to $Q$ respectively (via `CurveModel.pointEquivPlace`, $e_{\mathfrak{M}}$ and the first pullback projection) and such that `FakeEllipticCurve.HeckeNeighbour ℓ E E'` holds, i.e. there are mutually inverse-up-to-$\ell$ isogenies $\varphi : E \to E'$, $\psi : E' \to E$ respecting the group laws, the $\Lambda$-actions and the level structures, with $\psi \circ \varphi$ and $\varphi \circ \psi$ the action of $\ell$, neither being an isomorphism.
--
--   This identifies the Hecke correspondence at $\ell$ on the Shimura curve, read as a push–pull of divisors along the two degeneracy maps of the tower, with the $\ell$-isogeny (Hecke neighbour) relation on fake elliptic curves. It supplies the Hecke-correspondence compatibility required by the construction of a Shimura curve model with rigid moduli witness and Hecke tower, [`CerednikDrinfeld.exists_shimuraCurveModel_rigidModuliWitness_heckeTower_of_six_mul_dvd_of_neZero`](thm.html#CerednikDrinfeld.exists_shimuraCurveModel_rigidModuliWitness_heckeTower_of_six_mul_dvd_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_ModuliTowerWitness_mem_support_correspondence_single_iff_heckeNeighbour_of_two_mul_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.ModuliTowerWitness.mem_support_correspondence_single_iff_heckeNeighbour_of_two_mul_dvd
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 2 * N * q * q' ∣ D)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (X : Scheme.{0}) [hXint : IsIntegral X]
    (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hsmooth : Smooth πX) (hproper : IsProper πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ _) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ _) (s' : Spec (CommRingCat.of S') ⟶ _),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _) (P : SchemeHomOver s πX),
      ∃ E : FakeEllipticCurve Λ N k, pt k s E = P)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _)
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')
    (hsmooth1 : SmoothOfRelativeDimension 1 πX)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      IsIntegral (CategoryTheory.Limits.pullback πX s))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar_over : sbar ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away ((D : ℕ) : ℤ)))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) (he𝔐 : IsIso e𝔐)
    (he𝔐_snd : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)

    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT)
    (ℓ : HeckeTower.AwayPrime q q') (hℓN : ¬ (ℓ.1 : ℕ) ∣ N) (P Q : Place (AlgebraicClosure ℚ) Fbar) :
    Q ∈ (Divisor.correspondence (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1)) (Finsupp.single P 1)).support ↔
      ∃ E E' : FakeEllipticCurve Λ N (AlgebraicClosure ℚ),
        (pt _ sbar E).1 = (𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar ∧
        (pt _ sbar E').1 = (𝔐.pointEquivPlace.symm Q).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar ∧
        FakeEllipticCurve.HeckeNeighbour (ℓ.1 : ℕ) E E' := by sorry
