-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_finrankAlong_eq_arrowDegree_of_pt_pullback_of_two_mul_dvd_of_squarefree
-- name    : CerednikDrinfeld.QM.ModuliTowerWitnessD.finrankAlong_eq_arrowDegree_of_pt_pullback_of_two_mul_dvd_of_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/16814e0e-22cd-500c-afdd-d71b06897056
-- title:
--   Degrees of the degeneracy arrows of the QM tower
-- statement:
--   Fix natural numbers $N, q, q'$ with $N \neq 0$, $q$ and $q'$ prime, $q \nmid N$, $q' \nmid N$, $q' \neq q$ and $N$ squarefree, and a natural number $D$ divisible by $2Nqq'$. Let $a, b \in \mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $q \in v$ or $q' \in v$; let $\Lambda$ be a $\mathbb{Z}$-submodule that is a maximal order (an order, in the sense of containing $1$, being closed under multiplication, spanning over $\mathbb{Q}$ and finitely generated, and maximal among orders). Let $\bar{F}$ be a field over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` that is a curve over it (principal divisors, finite residue fields at all places, $\Omega$ free of rank one) and essentially of finite type. Let $\pi_X : X \to \operatorname{Spec} \mathbb{Z}[1/D]$ be a scheme over the localisation of $\mathbb{Z}$ away from $D$, $\bar{s}$ a $\overline{\mathbb{Q}}$-point of that base, and `pt` an assignment sending a fake elliptic curve $E$ over any commutative ring $S$ together with a base morphism $s$ to an $S$-point of $X$ over $s$, where a fake elliptic curve is an abelian scheme over $S$ with commutative relative group law, two-dimensional fibres, an action of $\Lambda$ satisfying the additivity, multiplicativity and trace conditions, and level-$N$ data. It is assumed that `pt` is constant on isomorphism classes, compatible with base change along ring homomorphisms $\varphi : S \to S'$ carrying $s'$ to $s$ and pullbacks of fake elliptic curves, and, over algebraically closed fields, surjective onto the points of $X$ over the given base morphism and injective up to isomorphism. Let $\mathfrak{M}$ be a curve model over $\overline{\mathbb{Q}}$ with function field $\bar{F}$ (an integral scheme, proper and smooth of relative dimension one over $\overline{\mathbb{Q}}$, with closed points in bijection with places), $e_{\mathfrak{M}}$ an isomorphism from $\mathfrak{M}.C$ to the pullback of $\pi_X$ along $\bar{s}$ with $e_{\mathfrak{M}}$ followed by the second projection equal to the structure map of $\mathfrak{M}$, `gal` a homomorphism from $\operatorname{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ to the semilinear automorphisms of $\bar{F}$, $\mathbb{T}$ a tower datum consisting of fields $F_\ell$ for primes $\ell \neq q, q'$, each a curve over $\overline{\mathbb{Q}}$ and essentially of finite type, together with two $\overline{\mathbb{Q}}$-algebra maps $\varphi_{(\ell,i)} : \bar{F} \to F_\ell$, $i \in \{0,1\}$, each finite and integral, `galT` semilinear Galois actions on the $F_\ell$, and $W$, $WT$ further semilinear automorphisms of $\bar{F}$ and of the $F_\ell$. Finally let `tw` be a witness of type `ModuliTowerWitnessD` for all these data, which in particular provides fake elliptic curves representing the places of $\bar{F}$ compatibly with `pt` and $e_{\mathfrak{M}}$, fake elliptic curves with extra level structure at $\ell$ representing the places of $F_\ell$ bijectively up to isomorphism, the compatibility of `gal` and `galT` with the given Galois action on $\overline{\mathbb{Q}}$, the triviality of $W$ and $WT$ on $\overline{\mathbb{Q}}$, and the agreement of level restriction along $\varphi_{(\ell,0)}$ with forgetting the extra level. The conclusion is that for every arrow $\alpha = (\ell, i)$ of the tower the degree of $F_\ell$ over $\bar{F}$, taken with respect to the algebra structure given by $\varphi_\alpha$, equals `HeckeTower.arrowDegree N α`, that is $\ell$ if $\ell \mid N$ and $\ell + 1$ otherwise.
--
--   This is the degree computation for the two degeneracy maps of the Hecke tower of quaternionic (Shimura) curves in the Čerednik–Drinfeld part of the argument: the extra level structure at $\ell$ on a fake elliptic curve has $\ell + 1$ choices when $\ell \nmid N$ and $\ell$ choices when $\ell \mid N$. It feeds the construction of Shimura curve models carrying a Hecke tower and the existence of descent intertwining data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_finrankAlong_eq_arrowDegree_of_pt_pullback_of_two_mul_dvd_of_squarefree.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
open AlgebraicCurve

theorem CerednikDrinfeld.QM.ModuliTowerWitnessD.finrankAlong_eq_arrowDegree_of_pt_pullback_of_two_mul_dvd_of_squarefree
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
    :
    ∀ α : HeckeTower.Arr q q', finrankAlong (AlgebraicClosure ℚ) (𝕋.φ α) = HeckeTower.arrowDegree N α := by sorry
