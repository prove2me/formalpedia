-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuliT_exists_hom_pullback_bijective_points
-- name    : CerednikDrinfeld.QM.IsCoarseModuliT.exists_hom_pullback_bijective_points
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/9c36788a-e93e-5fc3-8402-32b643653003
-- title:
--   Comparison morphism to a base-changed coarse moduli scheme
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, naturals $N,\ell$, commutative rings $B_0,B_1$ and a morphism $\iota:\operatorname{Spec}B_1\to\operatorname{Spec}B_0$. The parametrised objects over a commutative ring $S$ are pairs $u$ consisting of a `FakeEllipticCurve` for $\Lambda$ and $N$ over $S$ (a scheme $A\to\operatorname{Spec}S$ with a commutative relative group law, an abelian-scheme property bundle, fibres of dimension $2$, an additive $\Lambda$-action satisfying the trace condition, and a level subscheme) together with an extra level structure at $\ell$. Given $g:\mathcal{Y}\to\operatorname{Spec}B_0$ and a rule $\mathrm{ptT}$ sending each $s:\operatorname{Spec}S\to\operatorname{Spec}B_0$ and each such $u$ to a morphism $\operatorname{Spec}S\to\mathcal{Y}$ over $s$, assumed constant on `Iso`-classes, compatible with base change along ring maps in the sense of `IsPullback`, and surjective and injective up to isomorphism on points valued in algebraically closed fields; and given $\pi_Y:Y\to\operatorname{Spec}B_1$ with a rule $\mathrm{ptY}$ satisfying `IsCoarseModuliT` (the same four point laws plus the universal property against all such rules over $B_1$): then there is $h:Y\to\mathcal{Y}\times_{\operatorname{Spec}B_0}\operatorname{Spec}B_1$ with $h$ followed by the second projection equal to $\pi_Y$, such that for all $S$, $s:\operatorname{Spec}S\to\operatorname{Spec}B_1$ and $u$, the composite of $\mathrm{ptY}\,S\,s\,u$ with $h$ and the first projection is $\mathrm{ptT}\,S\,(s\circ\iota)\,u$; $h$ is the unique morphism over $B_1$ with that property; and for every algebraically closed field $k$ and every $s:\operatorname{Spec}k\to\operatorname{Spec}B_1$, composition with $h$ is injective on $k$-points of $Y$ over $s$ and hits every $k$-point of the fibre product over $s$.
--
--   This is the formal comparison between a coarse moduli scheme for fake elliptic curves with level $N$ and extra level $\ell$ over $B_1$ and the base change along $\iota$ of such a scheme over $B_0$: the induced morphism exists, is unique over $B_1$, and is bijective on points valued in algebraically closed fields. It is used to transport geometric properties across the base change, in the deduction that the coarse moduli scheme is geometrically reduced and geometrically connected under the hypotheses on the curve model and on invertibility of $2$ and $3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuliT_exists_hom_pullback_bijective_points.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.IsCoarseModuliT.exists_hom_pullback_bijective_points
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ)
    {B₀ B₁ : Type} [CommRing B₀] [CommRing B₁] (ι : Spec (CommRingCat.of B₁) ⟶ Spec (CommRingCat.of B₀))

    (𝒴 : Scheme.{0}) (g : 𝒴 ⟶ Spec (CommRingCat.of B₀))
    (ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s g)
    (ptT_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀))
      (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), FakeEllipticCurve.WithExtraLevel.Iso u u' → ptT S s u = ptT S s u')
    (ptT_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B₀)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
      ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
      FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' → (ptT S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptT S s u).1)
    (ptT_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₀))
      (y : SchemeHomOver s g), ∃ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k, ptT k s u = y)
    (ptT_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₀))
      (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ k), ptT k s u = ptT k s u' → FakeEllipticCurve.WithExtraLevel.Iso u u')

    (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of B₁))
    (ptY : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₁)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πY)
    (hY : IsCoarseModuliT Λ N ℓ Y πY ptY) :
    ∃ h : Y ⟶ pullback g ι,
      h ≫ pullback.snd g ι = πY ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₁))
        (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), (ptY S s u).1 ≫ h ≫ pullback.fst g ι = (ptT S (s ≫ ι) u).1) ∧
      (∀ h' : Y ⟶ pullback g ι, h' ≫ pullback.snd g ι = πY →
        (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₁))
          (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), (ptY S s u).1 ≫ h' ≫ pullback.fst g ι = (ptT S (s ≫ ι) u).1) →
        h' = h) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₁))
        (P P' : SchemeHomOver s πY), P.1 ≫ h = P'.1 ≫ h → P = P') ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₁))
        (Q : SchemeHomOver s (pullback.snd g ι)), ∃ P : SchemeHomOver s πY, P.1 ≫ h = Q.1) := by sorry
