-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_galT_of_coarse_of_two_mul_dvd
-- name    : CerednikDrinfeld.QM.exists_galT_of_coarse_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/0c4d3891-9001-529e-8d80-796c8c44334c
-- title:
--   Semilinear Galois actions on the upper function fields of the tower
-- statement:
--   Fix a non-zero natural number $N$, two distinct primes $q$ and $q'$ neither of which divides $N$, and a natural number $D$ divisible by $2Nqq'$; the base ring throughout is $\mathbb{Z}[1/D] =$ `Localization.Away ((D : ℕ) : ℤ)`. Fix rationals $a,b$ such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds for the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its non-zero elements invertible precisely when $v$ contains $q$ or $q'$; and fix a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order, that is, $\Lambda$ contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$ and is finitely generated, and every order containing $\Lambda$ equals $\Lambda$.
--
--   The lower data consist of: a field $\bar F$ over $\bar{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is a curve over $\bar{\mathbb{Q}}$ in the sense of `IsCurveOver` (principal divisors exist, all residue fields of places are finite over $\bar{\mathbb{Q}}$, and $\Omega_{\bar F/\bar{\mathbb{Q}}}$ is free of rank one) and is essentially of finite type; a scheme $X$ with a morphism $\pi_X : X \to \operatorname{Spec}\mathbb{Z}[1/D]$; a geometric point $\bar s : \operatorname{Spec}\bar{\mathbb{Q}} \to \operatorname{Spec}\mathbb{Z}[1/D]$ of the base; and a moduli map `pt` assigning, to every commutative ring $S$, every $S$-point $s$ of the base and every fake elliptic curve $E$ of `FakeEllipticCurve Λ N S` (an abelian scheme of relative dimension $2$ over $S$ with commutative relative group law, an action of $\Lambda$ by endomorphisms satisfying the trace condition, and a level-$N$ structure), a section of $\pi_X$ over $s$. Four hypotheses on `pt` are the first four clauses of `IsCoarseModuli` over $\mathbb{Z}[1/D]$, the universal property `univ` not being assumed: `pt_iso` (isomorphic fake elliptic curves have the same moduli point), `pt_pullback` (compatibility with base change along a ring homomorphism $\varphi : S \to S'$ over the base, for $E'$ a $\varphi$-pullback of $E$), `pt_surjective` and `pt_injective` (for every algebraically closed field $k$ and every $k$-point of the base, `pt` is onto the $k$-points of $X$ over that point, and two fake elliptic curves over $k$ with the same moduli point are isomorphic).
--
--   The rigidification of the geometric fibre consists of a curve model $\mathfrak{M}$ of $\bar F$ over $\bar{\mathbb{Q}}$ (an integral scheme $\mathfrak{M}.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec}\bar{\mathbb{Q}}$, together with an isomorphism of $\bar F$ with its function field over the base and a bijection between closed points and places matching valuation subrings with images of stalks), an isomorphism $e_{\mathfrak{M}} : \mathfrak{M}.C \to X \times_{\mathbb{Z}[1/D]} \operatorname{Spec}\bar{\mathbb{Q}}$ with $e_{\mathfrak{M}}$ followed by the second projection equal to $\mathfrak{M}.\mathrm{toBase}$, a group homomorphism $\mathrm{gal}$ from $\operatorname{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$ to $\operatorname{SemilinearAut}(\bar{\mathbb{Q}}, \bar F)$ (pairs consisting of a ring automorphism of $\bar F$ and one of $\bar{\mathbb{Q}}$ intertwined by the structure map), the hypothesis `hgal_base` that the base component of $\mathrm{gal}(\sigma)$ is $\sigma$, and `hgal_pt`, which states that for every $\sigma$ and every place $P$ of $\bar F$ over $\bar{\mathbb{Q}}$ the $\bar{\mathbb{Q}}$-point of $X$ attached to $\mathrm{gal}(\sigma) \cdot P$ through $\mathfrak{M}.\mathrm{pointEquivPlace}$, $e_{\mathfrak{M}}$ and the first projection equals $\operatorname{Spec}\sigma$ followed by the point attached to $P$.
--
--   The tower data consist of: a scheme $\mathcal{X}$ with a morphism $f$ to $\operatorname{Spec}\bar{\mathbb{Q}}$ and a moduli map $\mathrm{pt}_{\mathcal{X}}$ satisfying the full coarse moduli property `IsCoarseModuli Λ N 𝒳 f pt𝒳` over $\bar{\mathbb{Q}}$ (the four clauses above together with the universal property among such pairs), an isomorphism $g_{\mathcal{X}} : \mathcal{X} \to X \times_{\mathbb{Z}[1/D]} \operatorname{Spec}\bar{\mathbb{Q}}$ over $\bar{\mathbb{Q}}$ (`hg𝒳`) which transports $\mathrm{pt}_{\mathcal{X}}$ to `pt` (`hg𝒳pt`: for all $S$, all $s : \operatorname{Spec} S \to \operatorname{Spec}\bar{\mathbb{Q}}$ and all $E$, the moduli point of $E$ in $\mathcal{X}$ followed by $g_{\mathcal{X}}$ and the first projection is the moduli point of $E$ in $X$ over $s$ followed by $\bar s$); for each prime $\ell$ with $\ell \neq q, q'$ (the index type `HeckeTower.AwayPrime q q'`) a scheme $\mathcal{Y}_\ell$ over $\bar{\mathbb{Q}}$ with moduli map $\mathrm{pt}_T$ on pairs `FakeEllipticCurve.WithExtraLevel Λ N ℓ` (a fake elliptic curve together with an `ExtraLevel ℓ` subgroup scheme $K$ of rank $\ell^2$, disjoint from the level-$N$ structure and stable under $\Lambda$) satisfying `IsCoarseModuliT Λ N ℓ` (the analogous five clauses for pairs); degeneracy morphisms $d_0, d_1 : \mathcal{Y}_\ell \to \mathcal{X}$ characterised on moduli points by `hd₀` (the point of a pair $u$ followed by $d_0$ is the point of the underlying curve $u.1$) and `hd₁` (the point of $u$ followed by $d_1$ is the point of any $d$ admitting a level-$\ell$ isogeny from $u$ in the sense of `IsLevelIsogeny`); a choice $\mathrm{rep}$ of a fake elliptic curve over $\bar{\mathbb{Q}}$ for each place of $\bar F$, with `pt_rep` asserting that its moduli point in $X$ over $\bar s$ is the point of $X$ attached to that place through $\mathfrak{M}$ and $e_{\mathfrak{M}}$; a tower datum $\mathbb{T}$ of type `HeckeTower.TowerData q q' Fbar`, whose upper fields $\mathbb{T}.F_\ell$ are curves over $\bar{\mathbb{Q}}$, essentially of finite type, equipped with $\bar{\mathbb{Q}}$-algebra maps $\varphi_{(\ell, i)} : \bar F \to \mathbb{T}.F_\ell$ ($i \in \{0,1\}$) that are finite and integral; curve models $M_\ell$ of $\mathbb{T}.F_\ell$ over $\bar{\mathbb{Q}}$ with isomorphisms $e_\ell : (M_\ell).C \to \mathcal{Y}_\ell$ over $\bar{\mathbb{Q}}$ (`heℓiso`, `heℓ`); the hypothesis `hφpt` that for each $\ell$, each $i \in \{0,1\}$ and each place $R$ of $\mathbb{T}.F_\ell$, the $\bar{\mathbb{Q}}$-point of $X$ attached to the restriction of $R$ along $\varphi_{(\ell,i)}$ through $\mathfrak{M}$ and $e_{\mathfrak{M}}$ coincides with the point attached to $R$ through $M_\ell$, $e_\ell$, then $d_0$ if $i = 0$ and $d_1$ otherwise, then $g_{\mathcal{X}}$ and the first projection; and finally a choice $\mathrm{repT}_\ell$ of a pair over $\bar{\mathbb{Q}}$ for each place $R$ of $\mathbb{T}.F_\ell$, with `ptT_repT` asserting that its moduli point in $\mathcal{Y}_\ell$ over the identity of $\operatorname{Spec}\bar{\mathbb{Q}}$ is the point attached to $R$ through $M_\ell$ followed by $e_\ell$.
--
--   Under these hypotheses there exists a family of group homomorphisms $\mathrm{galT}_\ell : \operatorname{Gal}(\bar{\mathbb{Q}}/\mathbb{Q}) \to \operatorname{SemilinearAut}(\bar{\mathbb{Q}}, \mathbb{T}.F_\ell)$, indexed by the primes $\ell \neq q, q'$, such that:
--
--   first, for all $\ell$ and all $\sigma \in \operatorname{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$ the base component of $\mathrm{galT}_\ell(\sigma)$ is $\sigma$ itself;
--
--   second, for all $\ell$, all $\sigma$ and every place $P$ of $\mathbb{T}.F_\ell$ over $\bar{\mathbb{Q}}$ there are a pair $u$ in `FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)`, a morphism $g : u.1.A \to (\mathrm{repT}_\ell P).1.A$ and a proof that the square formed by $g$, the structure morphism of $u.1$, the structure morphism of $(\mathrm{repT}_\ell P).1$ and $\operatorname{Spec}\sigma$ is cartesian, such that the following four conditions hold, which together say that $u$ is a $\sigma$-base change of $\mathrm{repT}_\ell P$ in the sense of `FakeEllipticCurve.WithExtraLevel.IsPullback` and that it represents the place $\mathrm{galT}_\ell(\sigma) \cdot P$: (i) $g$ is a homomorphism for the relative group laws, that is, for every scheme $T$, every $t' : T \to \operatorname{Spec}\bar{\mathbb{Q}}$ and all points $Q, Q'$ of $u.1$ over $t'$, the product $u.1.L.\mathrm{mul}\,t'\,Q\,Q'$ followed by $g$ equals the product in $(\mathrm{repT}_\ell P).1$ over $t' \circ \operatorname{Spec}\sigma$ of the images $Q \cdot g$ and $Q' \cdot g$; (ii) $g$ intertwines the $\Lambda$-actions, $u.1.\mathrm{act}(x)$ followed by $g$ equalling $g$ followed by $(\mathrm{repT}_\ell P).1.\mathrm{act}(x)$ for every $x \in \Lambda$; (iii) $g$ carries both level structures forward: for every $T$, every $t'$ and every point $Q$ of $u.1$ over $t'$, if $Q$ factors through $u.1.\mathrm{lev}$ then $Q$ followed by $g$ factors through $(\mathrm{repT}_\ell P).1.\mathrm{lev}$, and if $Q$ factors through the extra level subgroup $u.2.\mathrm{levK}$ then $Q$ followed by $g$ factors through $(\mathrm{repT}_\ell P).2.\mathrm{levK}$; and (iv) $u$ is isomorphic, as a pair, to $\mathrm{repT}_\ell(\mathrm{galT}_\ell(\sigma) \cdot P)$, the isomorphism being one of $\bar{\mathbb{Q}}$-schemes compatible with the group laws, with the $\Lambda$-actions, and with the level-$N$ and level-$\ell$ structures in both directions.
--
--   This is the step that propagates the Galois action from the base curve to the upper layers of the Hecke tower attached to a quaternionic (fake elliptic curve) moduli problem: each upper function field $\mathbb{T}.F_\ell$ acquires an action of $\operatorname{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$ by semilinear automorphisms over $\sigma$, and on places this action is computed by base-changing the chosen representative pair along $\sigma$. It is used in the assembly of the moduli tower witness [`CerednikDrinfeld.QM.exists_moduliTowerWitness_of_two_mul_dvd_of_neZero_of_squarefree`](thm.html#CerednikDrinfeld.QM.exists_moduliTowerWitness_of_two_mul_dvd_of_neZero_of_squarefree), and rests on the coarse moduli property of the pair-schemes $\mathcal{Y}_\ell$ together with the dictionary between automorphisms of a smooth proper curve model over $\sigma$ and semilinear automorphisms of its function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_galT_of_coarse_of_two_mul_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.exists_galT_of_coarse_of_two_mul_dvd
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
    ∃ galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ),
      (∀ (ℓ : HeckeTower.AwayPrime q q') (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
    SemilinearAut.baseAut (galT ℓ σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)) ∧
      (∀ (ℓ : HeckeTower.AwayPrime q q') (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    ∃ (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) (AlgebraicClosure ℚ)) (g : u.1.A ⟶ (repT ℓ P).1.A)
      (hg : CategoryTheory.IsPullback g u.1.f (repT ℓ P).1.f
        (Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q Q' : SchemeHomOver t' u.1.f),
        (u.1.L.mul t' Q Q').1 ≫ g =
          ((repT ℓ P).1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)))
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩
            ⟨Q'.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q'.2]⟩).1) ∧
      (∀ x : ↥Λ, u.1.act x ≫ g = g ≫ (repT ℓ P).1.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t' u.1.f),
        (FactorsThrough u.1.lev Q → ∃ Q₀ : T ⟶ (repT ℓ P).1.C, Q₀ ≫ (repT ℓ P).1.lev = Q.1 ≫ g) ∧
        (FactorsThrough u.2.levK Q → ∃ Q₀ : T ⟶ (repT ℓ P).2.K, Q₀ ≫ (repT ℓ P).2.levK = Q.1 ≫ g)) ∧
      FakeEllipticCurve.WithExtraLevel.Iso u (repT ℓ (galT ℓ σ • P))) := by sorry
