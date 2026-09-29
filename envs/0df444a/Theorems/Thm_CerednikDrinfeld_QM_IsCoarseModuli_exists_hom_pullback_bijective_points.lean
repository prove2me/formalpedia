-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuli_exists_hom_pullback_bijective_points
-- name    : CerednikDrinfeld.QM.IsCoarseModuli.exists_hom_pullback_bijective_points
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/e43f4c81-c3e0-5932-b785-a339f16e911c
-- title:
--   Comparison morphism from a coarse moduli scheme to a base change
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, commutative rings $B_0,B_1$ and a morphism $\iota \colon \operatorname{Spec} B_1 \to \operatorname{Spec} B_0$. Let $f \colon \mathcal{X} \to \operatorname{Spec} B_0$ be a scheme over $B_0$ together with a rule $\mathrm{pt}$ assigning, to each commutative ring $S$, each $s \colon \operatorname{Spec} S \to \operatorname{Spec} B_0$ and each $E$ in `FakeEllipticCurve Λ N S` (a relative group scheme over $S$ with commutative relative group law, abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action satisfying the stated additivity, multiplicativity and trace conditions, and level data), a point $\mathrm{pt}(S,s,E)$ of $\mathcal{X}$ over $s$, i.e. a morphism $\operatorname{Spec} S \to \mathcal{X}$ whose composite with $f$ is $s$. Assume: $\mathrm{pt}$ is constant on `FakeEllipticCurve.Iso`-classes; for every ring map $\varphi \colon S \to S'$ with $\operatorname{Spec}\varphi$ followed by $s$ equal to $s'$ and every $E,E'$ with `FakeEllipticCurve.IsPullback φ E E'`, the point of $E'$ is $\operatorname{Spec}\varphi$ followed by the point of $E$; for every algebraically closed field $k$ and every $s \colon \operatorname{Spec} k \to \operatorname{Spec} B_0$ the map $E \mapsto \mathrm{pt}(k,s,E)$ is onto the points of $\mathcal{X}$ over $s$, and two curves with the same point are isomorphic. Let further $\pi_X \colon X \to \operatorname{Spec} B_1$ with a point rule $\mathrm{pt}_X$ satisfy `IsCoarseModuli Λ N X πX ptX`, that is the same four point-laws over $B_1$ together with the universal property that every scheme over $\operatorname{Spec} B_1$ carrying an iso-invariant, pullback-compatible point rule admits a unique morphism from $X$ over $\operatorname{Spec} B_1$ through which that rule factors. Then there is a morphism $h \colon X \to \mathcal{X} \times_{\operatorname{Spec} B_0} \operatorname{Spec} B_1$ such that: $h$ followed by the second projection is $\pi_X$; for all $S$, $s \colon \operatorname{Spec} S \to \operatorname{Spec} B_1$ and $E$, the point $\mathrm{pt}_X(S,s,E)$ followed by $h$ and the first projection equals $\mathrm{pt}(S, s \circ \iota, E)$; $h$ is the unique morphism with these two properties; and for every algebraically closed field $k$ and every $s \colon \operatorname{Spec} k \to \operatorname{Spec} B_1$, composition with $h$ is injective on points of $X$ over $s$ and every point of the fibre product over $s$ arises in this way.
--
--   This is the formal comparison statement that a coarse moduli scheme for fake elliptic curves with $\Lambda$-action and level-$N$ structure over $B_1$ maps to the base change along $\iota$ of any scheme over $B_0$ with the same four point-laws, bijectively on points valued in algebraically closed fields. It is the formal input to the identification of such coarse moduli schemes with base changes of Cherednik–Drinfel'd models, and is used in the comparison results away from the discriminant and under divisibility hypotheses, and in the exhaustive correspondence computation in the moduli tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuli_exists_hom_pullback_bijective_points.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.IsCoarseModuli.exists_hom_pullback_bijective_points
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ)
    {B₀ B₁ : Type} [CommRing B₀] [CommRing B₁] (ι : Spec (CommRingCat.of B₁) ⟶ Spec (CommRingCat.of B₀))

    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of B₀))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)),
      FakeEllipticCurve Λ N S → SchemeHomOver s f)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀))
      (E E' : FakeEllipticCurve Λ N S), FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B₀)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₀))
      (x : SchemeHomOver s f), ∃ E : FakeEllipticCurve Λ N k, pt k s E = x)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₀))
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')

    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of B₁))
    (ptX : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₁)),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hX : IsCoarseModuli Λ N X πX ptX) :
    ∃ h : X ⟶ pullback f ι,
      h ≫ pullback.snd f ι = πX ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₁))
        (E : FakeEllipticCurve Λ N S), (ptX S s E).1 ≫ h ≫ pullback.fst f ι = (pt S (s ≫ ι) E).1) ∧
      (∀ h' : X ⟶ pullback f ι, h' ≫ pullback.snd f ι = πX →
        (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₁))
          (E : FakeEllipticCurve Λ N S), (ptX S s E).1 ≫ h' ≫ pullback.fst f ι = (pt S (s ≫ ι) E).1) →
        h' = h) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₁))
        (P P' : SchemeHomOver s πX), P.1 ≫ h = P'.1 ≫ h → P = P') ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₁))
        (Q : SchemeHomOver s (pullback.snd f ι)), ∃ P : SchemeHomOver s πX, P.1 ≫ h = Q.1) := by sorry
