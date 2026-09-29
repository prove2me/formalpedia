-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuli_finite_etale_of_forall_local_via
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuli_finite_etale_of_forall_local_via
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/176b34dd-4a39-5c92-8164-b9427f059766
-- title:
--   Gluing a finite étale level-N cover of a fine moduli scheme
-- statement:
--   Let $q\neq q'$ be primes, let $a,b\in\mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'` (namely $0<a$ or $0<b$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$), and let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order (an order: contains $1$, closed under multiplication, $\mathbb{Q}$-spanning, finitely generated; and maximal among orders). Let $N\geq 1$, $m\geq 3$, and let $\mathcal{O}$ be a commutative ring in which $N$ and $m$ are units. Let $\pi_1:M_1\to\operatorname{Spec}\mathcal{O}$ together with the assignment $\mathrm{ptF}_1$, sending a commutative ring $S$, a morphism $s:\operatorname{Spec}S\to\operatorname{Spec}\mathcal{O}$ and an object of `FakeEllipticCurve.WithFullLevel Λ 1 m S` (a fake elliptic curve over $S$ with trivial extra level together with a full level-$m$ structure) to a section of $\pi_1$ over $s$, satisfy `IsFineModuli Λ 1 m M₁ π₁ ptF₁`: $\mathrm{ptF}_1$ is constant on isomorphism classes, compatible with pullback along ring maps, and for each $S$ and $s$ it is a bijection from isomorphism classes onto the points of $M_1$ over $s$. Assume the local relative representability hypothesis: for every commutative ring $S$ in which $N$ and $m$ are units and every $u$ in `FakeEllipticCurve.WithFullLevel Λ 1 m S` there are a scheme $Z$, a finite étale morphism $\zeta:Z\to\operatorname{Spec}S$, and an assignment $\mathrm{ptZ}$ which to every ring map $\varphi:S\to T$, every $u'$ over $T$ that is a pullback of $u$ along $\varphi$ (in the sense of `WithFullLevel.IsPullback`) and every extra level $K$ of order $N$ on $u'.1$ (a closed subscheme $K\to u'.1.A$ which is a subgroup for the relative group law, $N$-torsion, $\Lambda$-stable, disjoint from the given level structure, finite flat of finite presentation of fibre rank $N^2$ and geometrically isomorphic to $(\mathbb{Z}/N)^2$) attaches a section of $\zeta$ over $\operatorname{Spec}\varphi$, such that: $\mathrm{ptZ}$ depends on $K$ only through the collection of points factoring through $K.\mathrm{levK}$; $\mathrm{ptZ}$ is compatible with a further base change $\psi:T\to T'$, for $u''$ a pullback of $u$ along $\psi\circ\varphi$ via a morphism $g$ compatible with the group law, the $\Lambda$-action, the level and the full-level section, whenever every point factoring through $K''.\mathrm{levK}$ maps into $K'$ under $g$; every section of $\zeta$ over $\operatorname{Spec}\varphi$ is $\mathrm{ptZ}$ of some $K$; and $\mathrm{ptZ}\,K=\mathrm{ptZ}\,K'$ forces $K$ and $K'$ to have the same factoring points. Then there exist a scheme $M$, a morphism $f:M\to M_1$ and an assignment $\mathrm{ptF}$ on `FakeEllipticCurve.WithFullLevel Λ N m S` with values in sections of $f$ followed by $\pi_1$, such that `IsFineModuli Λ N m M (f ≫ π₁) ptF` holds and $f$ is finite and étale.
--
--   This is the gluing step in the construction of the fine moduli scheme for fake elliptic curves with extra level $N$ and full level $m$: the locally given finite étale schemes representing extra levels of order $N$ on the universal object are patched over an affine cover of the level-$(1,m)$ fine moduli scheme, rigidity for $m\ge 3$ making the patching data canonical. It is used by [`CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuli_finite_etale_of_isUnit`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuli_finite_etale_of_isUnit), where the local hypothesis is discharged.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuli_finite_etale_of_forall_local_via.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuli_finite_etale_of_forall_local_via
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] (m : ℕ) (hm : 3 ≤ m)
    (𝒪 : Type) [CommRing 𝒪] (hN : IsUnit ((N : ℕ) : 𝒪)) (hm' : IsUnit ((m : ℕ) : 𝒪))
    {M₁ : Scheme.{0}} {π₁ : M₁ ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF₁ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ 1 m S → SchemeHomOver s π₁}
    (hM₁ : IsFineModuli Λ 1 m M₁ π₁ ptF₁)
    (hloc : ∀ (S : Type) [CommRing S], IsUnit ((N : ℕ) : S) → IsUnit ((m : ℕ) : S) → ∀ u : FakeEllipticCurve.WithFullLevel Λ 1 m S,
      ∃ (Z : Scheme.{0}) (ζ : Z ⟶ Spec (CommRingCat.of S)) (_ : IsFinite ζ) (_ : Etale ζ)
        (ptZ : ∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T),
          FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → u'.1.ExtraLevel N → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ),

        (∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u') (K K' : u'.1.ExtraLevel N),
            (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of T)) (P : SchemeHomOver t u'.1.f),
              FactorsThrough K.levK P ↔ FactorsThrough K'.levK P) → ptZ T φ u' hu' K = ptZ T φ u' hu' K') ∧

        (∀ (T T' : Type) [CommRing T] [CommRing T'] (φ : S →+* T) (ψ : T →+* T')
            (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T) (u'' : FakeEllipticCurve.WithFullLevel Λ 1 m T')
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u')
            (hu'' : FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ) u u'')
            (K' : u'.1.ExtraLevel N) (K'' : u''.1.ExtraLevel N) (g : u''.1.A ⟶ u'.1.A),

            FakeEllipticCurve.IsPullbackVia ψ u'.1 u''.1 g →
            (u''.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom ψ) ≫ (u'.2.P).1 →
            (∀ {T₀ : Scheme.{0}} (t : T₀ ⟶ Spec (CommRingCat.of T')) (P : SchemeHomOver t u''.1.f),
              FactorsThrough K''.levK P → ∃ P₀ : T₀ ⟶ K'.K, P₀ ≫ K'.levK = P.1 ≫ g) →
              (ptZ T' (ψ.comp φ) u'' hu'' K'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptZ T φ u' hu' K').1) ∧

        (∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u')
            (z : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ), ∃ K : u'.1.ExtraLevel N, ptZ T φ u' hu' K = z) ∧
        (∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u')
            (K K' : u'.1.ExtraLevel N), ptZ T φ u' hu' K = ptZ T φ u' hu' K' →
            ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of T)) (P : SchemeHomOver t u'.1.f),
              FactorsThrough K.levK P ↔ FactorsThrough K'.levK P)) :
    ∃ (M : Scheme.{0}) (f : M ⟶ M₁)
      (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s (f ≫ π₁)),
      IsFineModuli Λ N m M (f ≫ π₁) ptF ∧ IsFinite f ∧ Etale f := by sorry
