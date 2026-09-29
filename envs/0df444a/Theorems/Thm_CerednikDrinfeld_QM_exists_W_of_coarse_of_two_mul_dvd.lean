-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_W_of_coarse_of_two_mul_dvd
-- name    : CerednikDrinfeld.QM.exists_W_of_coarse_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/82841e17-cb0f-5118-8df7-9494a9a2c325
-- title:
--   ℚ̄-linear Atkin–Lehner involutions at q and q'
-- statement:
--   Fix a nonzero natural number $N$ and primes $q \neq q'$ with $q \nmid N$ and $q' \nmid N$, and a natural number $D$ divisible by $2Nqq'$. Let $a,b \in \mathbb{Q}$ satisfy `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $a > 0$ or $b > 0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $q \in v$ or $q' \in v$; let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order (containing $1$, multiplicatively closed, $\mathbb{Q}$-spanning, finitely generated) and maximal among orders containing it. Let $\bar{F}$ be a field over $\bar{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, essentially of finite type and satisfying `IsCurveOver` (principal divisors of degree zero exist, residue fields of places are finite over $\bar{\mathbb{Q}}$, and $\Omega_{\bar F/\bar{\mathbb{Q}}}$ is free of rank one). The remaining hypotheses, summarised here, form five groups: (i) a scheme $X$ over $\mathrm{Spec}\,\mathbb{Z}[1/D]$ with a geometric point $\bar s$ over $\bar{\mathbb{Q}}$ and a moduli map $\mathrm{pt}$ sending fake elliptic curves `FakeEllipticCurve Λ N S` to $X$-points over $s$, assumed invariant under isomorphism, compatible with pullback along ring maps, and bijective on isomorphism classes over algebraically closed fields; (ii) a curve model $\mathfrak{M}$ of $\bar F$ over $\bar{\mathbb{Q}}$ together with an isomorphism $e_{\mathfrak{M}} : \mathfrak{M}.C \to X \times_{\mathbb{Z}[1/D]} \bar{\mathbb{Q}}$ over $\bar{\mathbb{Q}}$, and a homomorphism $\mathrm{gal}$ from $\mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$ to the semilinear automorphisms of $\bar F/\bar{\mathbb{Q}}$ lifting $\sigma$ on the base and acting on places compatibly with $\mathrm{Spec}\,\sigma$ on the associated $X$-points; (iii) a coarse moduli scheme $(\mathcal{X}, f, \mathrm{pt}_{\mathcal{X}})$ for `FakeEllipticCurve Λ N ·` over $\bar{\mathbb{Q}}$ in the sense of `IsCoarseModuli`, identified by an isomorphism $g_{\mathcal{X}}$ with $X \times_{\mathbb{Z}[1/D]} \bar{\mathbb{Q}}$ compatibly with $\mathrm{pt}$; (iv) for every prime $\ell \notin \{q,q'\}$ a coarse moduli scheme $(\mathcal{Y}_\ell, g_\ell, \mathrm{pt}_{T,\ell})$ for pairs `FakeEllipticCurve.WithExtraLevel Λ N ℓ` in the sense of `IsCoarseModuliT`, with degeneracy morphisms $d_0, d_1 : \mathcal{Y}_\ell \to \mathcal{X}$ characterised by $d_0$ forgetting the extra level and $d_1$ sending the class of $u$ to that of any $d$ with `FakeEllipticCurve.IsLevelIsogeny ℓ u d`; (v) a choice $\mathrm{rep}$ of a fake elliptic curve over $\bar{\mathbb{Q}}$ for each place $P$ of $\bar F/\bar{\mathbb{Q}}$, whose moduli point is the $\bar{\mathbb{Q}}$-point of $\mathfrak{M}.C$ attached to $P$ by $\mathfrak{M}$.`pointEquivPlace`, read in $X$ through $e_{\mathfrak{M}}$ and the projection. The conclusion asserts the existence of two semilinear automorphisms $W_0, W_1$ of $\bar F$ over $\bar{\mathbb{Q}}$ whose base automorphisms are the identity on $\bar{\mathbb{Q}}$, such that for every place $P$ one has `(rep P).IsAtkinLehnerQuotient q (rep (W 0 • P))` and `(rep P).IsAtkinLehnerQuotient q' (rep (W 1 • P))`: there are morphisms $\varphi, \psi$ in both directions between the underlying abelian schemes, over $\mathrm{Spec}\,\bar{\mathbb{Q}}$, additive for the relative group laws, commuting with the $\Lambda$-actions, with $\varphi \psi$ and $\psi \varphi$ equal to the action of the scalar $q$ (respectively $q'$) whenever that scalar lies in $\Lambda$, with $\varphi$ killing exactly those points annihilated by every $m \in \Lambda$ of reduced norm divisible by $q$ (respectively $q'$), and carrying level structures to level structures.
--
--   This is the construction of the two Atkin–Lehner involutions at the ramified primes $q$ and $q'$ on the Shimura curve attached to the indefinite quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ with level $N$: they are produced as automorphisms of the function field $\bar F$ fixing $\bar{\mathbb{Q}}$ and are identified through the moduli interpretation, the translated place being represented by the Atkin–Lehner quotient of the representing fake elliptic curve. It feeds the assembly of the moduli tower witness used in the Čerednik–Drinfeld description of the curve at $q$ and $q'$, via [`CerednikDrinfeld.QM.exists_moduliTowerWitness_of_two_mul_dvd_of_neZero_of_squarefree`](thm.html#CerednikDrinfeld.QM.exists_moduliTowerWitness_of_two_mul_dvd_of_neZero_of_squarefree).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_W_of_coarse_of_two_mul_dvd.lean

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

theorem CerednikDrinfeld.QM.exists_W_of_coarse_of_two_mul_dvd
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
      (pt _ sbar (rep P)).1 = (𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar) :
    ∃ W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar,
      (∀ (i : Fin 2) (c : AlgebraicClosure ℚ), SemilinearAut.baseAut (W i) c = c) ∧
      (∀ P : Place (AlgebraicClosure ℚ) Fbar, (rep P).IsAtkinLehnerQuotient q (rep (W 0 • P))) ∧
      (∀ P : Place (AlgebraicClosure ℚ) Fbar, (rep P).IsAtkinLehnerQuotient q' (rep (W 1 • P))) := by sorry
