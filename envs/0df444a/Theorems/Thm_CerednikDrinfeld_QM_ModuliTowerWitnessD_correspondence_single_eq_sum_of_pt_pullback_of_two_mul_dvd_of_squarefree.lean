-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_correspondence_single_eq_sum_of_pt_pullback_of_two_mul_dvd_of_squarefree
-- name    : CerednikDrinfeld.QM.ModuliTowerWitnessD.correspondence_single_eq_sum_of_pt_pullback_of_two_mul_dvd_of_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/cfdfd3e5-5c8f-566b-a081-452123618e93
-- title:
--   Push-pull of a place as a sum of ℓ+1 places
-- statement:
--   Fix non-zero $N$ and primes $q \neq q'$ with $q \nmid N$, $q' \nmid N$ and $N$ squarefree, and $D$ with $2Nqq' \mid D$. Let $a,b \in \mathbb{Q}$ satisfy `IsIndefiniteRamifiedExactlyAt`, i.e. $a>0$ or $b>0$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$; let $\Lambda$ be a maximal order (an order in the sense of containing $1$, closed under multiplication, $\mathbb{Q}$-spanning and finitely generated, maximal among orders above it). Let $\bar F$ be a field, a curve over $\bar{\mathbb{Q}} =$ `AlgebraicClosure ℚ` in the sense of `IsCurveOver` and essentially of finite type, and let $\pi_X : X \to \operatorname{Spec} \mathbb{Z}[1/D]$ be a scheme over $\mathbb{Z}[1/D]$ with a geometric point $\bar s$. The assignment `pt` sends a commutative ring $S$, a map $s : \operatorname{Spec} S \to \operatorname{Spec} \mathbb{Z}[1/D]$ and a fake elliptic curve over $S$ of level $N$ for $\Lambda$ to a point of $X$ over $s$, and is assumed to be invariant under `FakeEllipticCurve.Iso`, compatible with base change along ring maps (for pullbacks of fake elliptic curves), and, over algebraically closed fields, surjective and injective up to isomorphism. Further data: a curve model $\mathfrak{M}$ of $\bar F$ over $\bar{\mathbb{Q}}$ together with an isomorphism $e_{\mathfrak{M}}$ onto the fibre product of $\pi_X$ and $\bar s$ compatible with the structure maps, semilinear Galois actions `gal`, `galT`, involutions $W$, $WT$, a Hecke tower `TowerData` $\mathbb{T}$ away from $q,q'$ over $\bar F$, and a witness `tw : ModuliTowerWitnessD` for all of these. Finally let $\ell$ be a prime distinct from $q,q'$ with $\ell \nmid N$, let $P$ be a place of $\bar F$ over $\bar{\mathbb{Q}}$, and let $E$ be a fake elliptic curve over $\bar{\mathbb{Q}}$ whose moduli point `pt` equals the point of $X$ attached to $P$ through $\mathfrak{M}.\mathrm{pointEquivPlace}$ and $e_{\mathfrak{M}}$. The conclusion: there are families $K : \mathrm{Fin}(\ell+1) \to E.\mathrm{ExtraLevel}\,\ell$ of extra $\ell$-level structures on $E$ and $Q : \mathrm{Fin}(\ell+1) \to$ places of $\bar F$ such that the $K_i$ are pairwise distinguished by which $\bar{\mathbb{Q}}$-points of $E$ factor through them, each pair $\langle E, K_i \rangle$ is $\ell$-level-isogenous (`IsLevelIsogeny`) to `tw.rep (Q i)`, and the Hecke correspondence `Divisor.correspondence` — pushforward along $\mathbb{T}.\varphi(\ell,1)$ of the pullback along $\mathbb{T}.\varphi(\ell,0)$ — sends the divisor $[P]$ to $\sum_{i} [Q_i]$.
--
--   This is the multiplicity statement for the degeneracy correspondence on the Hecke tower of a Shimura curve attached to an indefinite quaternion algebra ramified exactly at $q$ and $q'$: the image of a single place under push-pull is the sum of the $\ell+1$ places parametrising the $\ell$-isogeny quotients of the corresponding fake elliptic curve. It supplies the multiplicity clause of the rigid moduli package assembled in [`CerednikDrinfeld.exists_shimuraCurveModel_rigidModuliWitness_heckeTower_of_six_mul_dvd_of_neZero`](thm.html#CerednikDrinfeld.exists_shimuraCurveModel_rigidModuliWitness_heckeTower_of_six_mul_dvd_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_correspondence_single_eq_sum_of_pt_pullback_of_two_mul_dvd_of_squarefree.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld NeronModelInfra
open CerednikDrinfeld.QM
open AlgebraicCurve

theorem CerednikDrinfeld.QM.ModuliTowerWitnessD.correspondence_single_eq_sum_of_pt_pullback_of_two_mul_dvd_of_squarefree
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
    (ℓ : HeckeTower.AwayPrime q q') (hℓN : ¬ (ℓ.1 : ℕ) ∣ N) (P : Place (AlgebraicClosure ℚ) Fbar)
    (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) (hE : (pt _ sbar E).1 = (𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar) :
    ∃ (K : Fin ((ℓ.1 : ℕ) + 1) → E.ExtraLevel (ℓ.1 : ℕ)) (Q : Fin ((ℓ.1 : ℕ) + 1) → Place (AlgebraicClosure ℚ) Fbar),
      (∀ i j : Fin ((ℓ.1 : ℕ) + 1),
          (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f,
            FactorsThrough (K i).levK x ↔ FactorsThrough (K j).levK x) → i = j) ∧
      (∀ i : Fin ((ℓ.1 : ℕ) + 1),
          FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ)
            (⟨E, K i⟩ : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) (AlgebraicClosure ℚ)) (tw.rep (Q i))) ∧
      Divisor.correspondence (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1)) (Finsupp.single P 1) =
        Finset.univ.sum (fun i : Fin ((ℓ.1 : ℕ) + 1) => Finsupp.single (Q i) 1) := by sorry
