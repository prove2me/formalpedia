-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_moduliTowerWitness_of_two_mul_dvd_of_neZero_of_squarefree
-- name    : CerednikDrinfeld.QM.exists_moduliTowerWitness_of_two_mul_dvd_of_neZero_of_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/132a46a0-6ec3-5c0e-81f1-423b60523ba8
-- title:
--   Existence of a moduli tower witness for fake elliptic curves
-- statement:
--   Fix naturals $N \neq 0$ and primes $q \neq q'$ with $q \nmid N$, $q' \nmid N$ and $N$ squarefree, and a nonzero natural $D$ divisible by $2Nqq'$. Fix $a,b \in \mathbb{Q}$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0 < a$ or $0 < b$ and, for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $q \in v$ or $q' \in v$; and let $\Lambda$ be a $\mathbb{Z}$-submodule which is an order (containing $1$, multiplicatively closed, $\mathbb{Q}$-spanning, finitely generated) maximal among orders. Let $Fbar$ be a field over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is a curve over it in the sense of `IsCurveOver` (principal divisors of degree zero, finite residue extensions, $\Omega$ free of rank one) and essentially of finite type. Let $\pi_X : X \to \operatorname{Spec} \mathbb{Z}[1/D]$ be a scheme over the localisation of $\mathbb{Z}$ away from $D$, $\bar{s} : \operatorname{Spec} \overline{\mathbb{Q}} \to \operatorname{Spec} \mathbb{Z}[1/D]$ a point, and $\mathrm{pt}$ an assignment sending, for every commutative ring $S$ and every $s : \operatorname{Spec} S \to \operatorname{Spec} \mathbb{Z}[1/D]$, a fake elliptic curve $E$ over $S$ (an abelian scheme with commutative relative group law, all fibres of dimension $2$, a $\Lambda$-action satisfying the trace condition, and level data `lev`) to a morphism $\operatorname{Spec} S \to X$ over $s$; it is assumed constant on `FakeEllipticCurve.Iso`-classes, compatible with base change along ring maps $\varphi : S \to S'$ and pullbacks of fake elliptic curves, and, over algebraically closed fields, surjective onto points over $s$ and injective up to isomorphism. Let $\mathfrak{M}$ be a `CurveModel` of $Fbar$ over $\overline{\mathbb{Q}}$ (an integral proper smooth relative-dimension-one scheme together with an identification of $Fbar$ with its function field and a bijection of its closed points with the places of $Fbar/\overline{\mathbb{Q}}$), let $e_{\mathfrak{M}} : \mathfrak{M}.C \to X \times_{\mathbb{Z}[1/D]} \operatorname{Spec} \overline{\mathbb{Q}}$ be an isomorphism whose composite with the second projection is $\mathfrak{M}.\mathrm{toBase}$, and let $\mathrm{gal}$ be a homomorphism from $\operatorname{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ to the group of pairs of ring automorphisms of $Fbar$ and of $\overline{\mathbb{Q}}$ compatible with the structure map, whose base component on $\sigma$ is $\sigma$, and such that for every $\sigma$ and every place $P$ the $\overline{\mathbb{Q}}$-point of $X$ attached to $\mathrm{gal}(\sigma) \cdot P$ (via $\mathfrak{M}.\mathrm{pointEquivPlace}$, $e_{\mathfrak{M}}$ and the first projection) is $\operatorname{Spec}(\sigma)$ followed by the point attached to $P$. The conclusion asserts the existence of a tower datum $\mathbb{T}$ over $Fbar$ for the primes $\ell \neq q,q'$ (fields $F_\ell$ that are curves over $\overline{\mathbb{Q}}$, with $\overline{\mathbb{Q}}$-algebra maps $Fbar \to F_{\alpha.1}$ indexed by `Arr q q'`, finite and integral along each), of semilinear Galois actions $\mathrm{galT}_\ell$ on each $F_\ell$, and of two semilinear automorphisms $W_0,W_1$ of $Fbar$ and $WT_{\ell,0},WT_{\ell,1}$ of each $F_\ell$, for which the type `ModuliTowerWitnessD` of these data is nonempty: that is, there are representatives $\mathrm{rep}(P)$, fake elliptic curves over $\overline{\mathbb{Q}}$ indexed by the places $P$ of $Fbar$, with $\mathrm{pt}$ of $\mathrm{rep}(P)$ the point of $X$ attached to $P$, representatives $\mathrm{repT}_\ell(P)$ among fake elliptic curves with extra level $\ell$ indexed by the places of $F_\ell$, bijective up to `WithExtraLevel.Iso`, base components of $\mathrm{galT}_\ell(\sigma)$ equal to $\sigma$ and of $W_i$, $WT_{\ell,i}$ trivial on $\overline{\mathbb{Q}}$, the restriction along the first leg $\mathbb{T}.\varphi(\ell,0)$ identifying $\mathrm{repT}_\ell(P)$ with $\mathrm{rep}$ of the restricted place after forgetting the extra level, and the remaining compatibilities recorded by `ModuliTowerWitnessD`.
--
--   This is the construction step supplying the Hecke tower of Shimura curves attached to an indefinite quaternion algebra ramified exactly at $q$ and $q'$: from a coarse moduli package for fake elliptic curves with level $N$ over $\mathbb{Z}[1/D]$ and a smooth proper model of its geometric fibre, it produces the auxiliary function fields at the primes $\ell$ away from $q,q'$, together with the degeneracy legs, the semilinear Galois actions and the Atkin–Lehner involutions, all matched with the moduli interpretation. It is used by the statements producing a Shimura curve model with a rigid moduli witness and a Hecke tower, and by the two descent-intertwining statements at the places $q$ and $q'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_moduliTowerWitness_of_two_mul_dvd_of_neZero_of_squarefree.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
open AlgebraicCurve

theorem CerednikDrinfeld.QM.exists_moduliTowerWitness_of_two_mul_dvd_of_neZero_of_squarefree
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hNsq : Squarefree N)
    (D : ℕ) [NeZero D] (hD : 2 * N * q * q' ∣ D)

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
    :
    ∃ (𝕋 : HeckeTower.TowerData q q' Fbar)
      (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
      (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar)
      (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ)),
      Nonempty (ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT) := by sorry
