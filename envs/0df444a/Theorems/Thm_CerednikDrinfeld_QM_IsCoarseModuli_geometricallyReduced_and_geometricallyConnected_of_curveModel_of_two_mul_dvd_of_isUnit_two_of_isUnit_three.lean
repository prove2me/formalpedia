-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuli_geometricallyReduced_and_geometricallyConnected_of_curveModel_of_two_mul_dvd_of_isUnit_two_of_isUnit_three
-- name    : CerednikDrinfeld.QM.IsCoarseModuli.geometricallyReduced_and_geometricallyConnected_of_curveModel_of_two_mul_dvd_of_isUnit_two_of_isUnit_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/b3f3f8a2-5398-5ead-8329-cfbd30311124
-- title:
--   Geometric reducedness and connectedness of the generic fibre
-- statement:
--   Fix natural numbers $N \neq 0$ and primes $q \neq q'$, and a natural number $D$ divisible by $2Nqq'$. Let $a,b \in \mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0 < a$ or $0 < b$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, its completion $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$; let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among the orders containing it. Let $\bar F$ be a field over $\bar{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is essentially of finite type and satisfies `IsCurveOver` (principal divisors, finite residue extensions at every place, and $\Omega_{\bar F/\bar{\mathbb{Q}}}$ free of rank one). Over the base $\mathbb{Z}[1/D] =$ `Localization.Away (D : ℤ)` one is given a scheme $X$ with a morphism $\pi_X$ to $\operatorname{Spec}\mathbb{Z}[1/D]$, a point $\bar s : \operatorname{Spec}\bar{\mathbb{Q}} \to \operatorname{Spec}\mathbb{Z}[1/D]$, and an assignment $\mathrm{pt}$ sending each fake elliptic curve with $\Lambda$-action and level-$N$ structure over a commutative ring $S$, together with an $S$-point $s$ of the base, to a morphism $\operatorname{Spec} S \to X$ over $s$; $\mathrm{pt}$ is assumed to be invariant under isomorphism of fake elliptic curves, compatible with pullback along ring maps, and bijective on isomorphism classes over algebraically closed fields. Further, $\mathfrak{M}$ is a curve model of $\bar F/\bar{\mathbb{Q}}$ (an integral scheme $\mathfrak{M}.C$, proper and smooth of relative dimension one over $\operatorname{Spec}\bar{\mathbb{Q}}$, with $\bar F$ identified with its function field compatibly with the base, closed points in bijection with the places of $\bar F/\bar{\mathbb{Q}}$ matching stalks with valuation rings, and every finite set of points contained in an affine open), and $e_{\mathfrak{M}} : \mathfrak{M}.C \to X \times_{\operatorname{Spec}\mathbb{Z}[1/D]} \operatorname{Spec}\bar{\mathbb{Q}}$ is an isomorphism whose composite with the second projection is $\mathfrak{M}.\mathrm{toBase}$. Finally let $\mathcal{O}_0$ be a domain of characteristic zero with fraction field $K_0$, in which $N$, $2$, $3$ and some $m_0 \geq 3$ are units, and let $f_0 : \mathcal{X}_0 \to \operatorname{Spec}\mathcal{O}_0$ together with $\mathrm{pt}_0$ satisfy `IsCoarseModuli` for $\Lambda$ and $N$ (the four conditions above together with the universal property among such point-assignments), with $\mathcal{X}_0$ integral and $f_0$ flat, separated, locally of finite type and quasi-compact. The conclusion is that the projection $\mathcal{X}_0 \times_{\operatorname{Spec}\mathcal{O}_0} \operatorname{Spec} K_0 \to \operatorname{Spec} K_0$ is geometrically reduced and geometrically connected.
--
--   This is the statement that the generic fibre of a coarse moduli scheme for fake elliptic curves with $\Lambda$-action and level-$N$ structure, over a characteristic-zero base domain in which $N$, $2$, $3$ and some $m_0 \geq 3$ are invertible, is a geometrically reduced and geometrically connected curve, the connectedness being transported from the smooth proper model $\mathfrak{M}$ of the Shimura curve over $\bar{\mathbb{Q}}$ through the comparison isomorphism $e_{\mathfrak{M}}$ and the universal property of the coarse moduli scheme. It feeds the construction of the Čerednik–Drinfeld moduli towers and their descent data used later in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuli_geometricallyReduced_and_geometricallyConnected_of_curveModel_of_two_mul_dvd_of_isUnit_two_of_isUnit_three.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra AlgebraicCurve

theorem CerednikDrinfeld.QM.IsCoarseModuli.geometricallyReduced_and_geometricallyConnected_of_curveModel_of_two_mul_dvd_of_isUnit_two_of_isUnit_three
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
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

    (𝒪₀ : Type) [CommRing 𝒪₀] [IsDomain 𝒪₀] [CharZero 𝒪₀]
    (K₀ : Type) [Field K₀] [Algebra 𝒪₀ K₀] [IsFractionRing 𝒪₀ K₀]
    (hN₀ : IsUnit ((N : ℕ) : 𝒪₀)) (h2₀ : IsUnit ((2 : ℕ) : 𝒪₀)) (h3₀ : IsUnit ((3 : ℕ) : 𝒪₀)) (m₀ : ℕ) (hm₀ : 3 ≤ m₀) (hm₀u : IsUnit ((m₀ : ℕ) : 𝒪₀))
    (𝒳₀ : Scheme.{0}) (f₀ : 𝒳₀ ⟶ Spec (CommRingCat.of 𝒪₀))
    (pt₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)), FakeEllipticCurve Λ N S → SchemeHomOver s f₀)
    (h𝒳₀ : IsCoarseModuli Λ N 𝒳₀ f₀ pt₀)
    [IsIntegral 𝒳₀] [Flat f₀] [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀] :
    GeometricallyReduced (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap 𝒪₀ K₀)))) ∧
    GeometricallyConnected (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap 𝒪₀ K₀)))) := by sorry
