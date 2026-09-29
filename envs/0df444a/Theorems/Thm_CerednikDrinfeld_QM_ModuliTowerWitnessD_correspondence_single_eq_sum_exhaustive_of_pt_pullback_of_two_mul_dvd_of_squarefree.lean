-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_correspondence_single_eq_sum_exhaustive_of_pt_pullback_of_two_mul_dvd_of_squarefree
-- name    : CerednikDrinfeld.QM.ModuliTowerWitnessD.correspondence_single_eq_sum_exhaustive_of_pt_pullback_of_two_mul_dvd_of_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/c449db6f-716c-58c6-b6f3-85c038377c1b
-- title:
--   Push–pull of a single place over all extra levels at ℓ
-- statement:
--   Fix natural numbers $N\neq 0$ and primes $q,q'$ with $q\nmid N$, $q'\nmid N$, $q'\neq q$ and $N$ squarefree, and a natural number $D$ divisible by $2Nqq'$. Fix $a,b\in\mathbb{Q}$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($a>0$ or $b>0$) and, for a finite place $v$ of $\mathbb{Q}$, the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ lies over $q$ or $q'$; fix a maximal order $\Lambda$ in it (a finitely generated $\mathbb{Z}$-submodule containing $1$, closed under multiplication, $\mathbb{Q}$-spanning the algebra, and maximal among such). Let $\bar F$ be a field, essentially of finite type over $\bar{\mathbb{Q}}$ and a curve over it (principal divisors exist, residue fields of places are finite over $\bar{\mathbb{Q}}$, and $\Omega_{\bar F/\bar{\mathbb{Q}}}$ is free of rank one). Let $\pi_X\colon X\to\operatorname{Spec}\mathbb{Z}[1/D]$ be a scheme over $\mathbb{Z}[1/D]$, let $\bar s$ be the $\bar{\mathbb{Q}}$-point of the base, and let `pt` attach to every ring $S$, every $S$-point $s$ of the base and every fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ structure a morphism $\operatorname{Spec}S\to X$ over $s$; `pt` is assumed to depend only on the isomorphism class, to be compatible with base change along ring maps (for the underlying morphisms), and, over algebraically closed fields, to be surjective onto points of $X$ and injective on isomorphism classes. Let $\mathfrak{M}$ be a curve model of $\bar F$ over $\bar{\mathbb{Q}}$ (an integral, proper, relative-dimension-one smooth $\bar{\mathbb{Q}}$-scheme with function field identified with $\bar F$ and closed points in bijection with places), let $e_{\mathfrak M}\colon\mathfrak{M}.C\to X\times_{\mathbb{Z}[1/D]}\bar{\mathbb{Q}}$ be an isomorphism compatible with the structure morphisms, let `gal` be a homomorphism from $\operatorname{Aut}(\bar{\mathbb{Q}}/\mathbb{Q})$ to the semilinear automorphisms of $\bar F$ over $\bar{\mathbb{Q}}$, let $\mathbb{T}$ be tower data over $\bar F$ for the pair $(q,q')$ (for each prime $\ell\neq q,q'$ a curve field $F_\ell$ over $\bar{\mathbb{Q}}$ together with finite integral $\bar{\mathbb{Q}}$-algebra maps $\varphi_{\ell,0},\varphi_{\ell,1}\colon\bar F\to F_\ell$), and let `galT`, $W$, `WT` be the corresponding semilinear data. Let `tw` be a `ModuliTowerWitnessD` for all of these, which in particular provides for each place $P$ of $\bar F$ a fake elliptic curve $\mathrm{rep}(P)$ over $\bar{\mathbb{Q}}$ whose `pt`-image is the point of $X$ attached to $P$, and parametrises pairs (fake elliptic curve, extra level at $\ell$) by places of $F_\ell$ compatibly with the leg $\varphi_{\ell,0}$. Finally let $\ell$ be a prime different from $q$ and $q'$, let $P$ be a place of $\bar F$, and let $E$ be a fake elliptic curve over $\bar{\mathbb{Q}}$ whose `pt`-image is the point of $X$ attached to $P$ through $\mathfrak{M}.\mathrm{pointEquivPlace}$, $e_{\mathfrak M}$ and the first projection. Then there exist $n\in\mathbb{N}$, extra levels $K_0,\dots,K_{n-1}$ at $\ell$ on $E$ (closed subschemes of $E$ that are $\ell$-torsion subgroups, stable under $\Lambda$, finite flat of fibre rank $\ell^2$ with geometric fibres $\cong(\mathbb{Z}/\ell)^2$, meeting the level-$N$ structure trivially) and places $Q_0,\dots,Q_{n-1}$ of $\bar F$ such that: the $K_i$ are pairwise distinct as subfunctors of $\bar{\mathbb{Q}}$-points of $E$; every extra level at $\ell$ on $E$ has the same $\bar{\mathbb{Q}}$-points as some $K_i$; for each $i$ the pair $(E,K_i)$ is $\ell$-level isogenous to $\mathrm{tw}.\mathrm{rep}(Q_i)$, i.e. there is a pair of mutually dual $\Lambda$-equivariant isogenies composing to multiplication by $\ell$, the first with kernel exactly $K_i$ and carrying the level-$N$ structure of $E$ into that of $\mathrm{rep}(Q_i)$; and the push–pull correspondence, the pullback along $\varphi_{\ell,0}$ followed by the pushforward along $\varphi_{\ell,1}$ (using their integrality), sends the divisor $[P]$ to $\sum_{i<n}[Q_i]$. No value for $n$ is asserted.
--
--   This is the moduli-theoretic computation of the Hecke correspondence at a prime $\ell\neq q,q'$ on a degree-one divisor of the Shimura curve $\bar F$: the image of $[P]$ is the multiplicity-free sum over the places representing the quotients of $E$ by its extra levels at $\ell$, and the family of extra levels used is exhaustive, so the statement covers both $\ell\nmid N$ and $\ell\mid N$. It is cited in the derivation of the commutation of the correspondences, in the specialised single-place formula, and in the identification of the degrees of the tower legs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_correspondence_single_eq_sum_exhaustive_of_pt_pullback_of_two_mul_dvd_of_squarefree.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
open AlgebraicCurve

theorem CerednikDrinfeld.QM.ModuliTowerWitnessD.correspondence_single_eq_sum_exhaustive_of_pt_pullback_of_two_mul_dvd_of_squarefree
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
    (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) Fbar)
    (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) (hE : (pt _ sbar E).1 = (𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar) :
    ∃ (n : ℕ) (K : Fin n → E.ExtraLevel (ℓ.1 : ℕ)) (Q : Fin n → Place (AlgebraicClosure ℚ) Fbar),
      (∀ i j : Fin n,
          (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f,
            FactorsThrough (K i).levK x ↔ FactorsThrough (K j).levK x) → i = j) ∧
      (∀ K' : E.ExtraLevel (ℓ.1 : ℕ), ∃ i : Fin n,
          ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f,
            FactorsThrough K'.levK x ↔ FactorsThrough (K i).levK x) ∧
      (∀ i : Fin n,
          FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ)
            (⟨E, K i⟩ : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) (AlgebraicClosure ℚ)) (tw.rep (Q i))) ∧
      Divisor.correspondence (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1)) (Finsupp.single P 1) =
        Finset.univ.sum (fun i : Fin n => Finsupp.single (Q i) 1) := by sorry
