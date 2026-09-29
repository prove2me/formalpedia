-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_finite_etale_represents_extraLevel
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_finite_etale_represents_extraLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/3d51c95a-36d7-533d-83e3-e75c36023647
-- title:
--   Extra levels of order N represented by a finite étale scheme
-- statement:
--   Fix distinct primes $q' \neq q$ and rationals $a,b$ such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds: $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is a maximal order (an order: containing $1$, multiplicatively closed, finitely generated, spanning over $\mathbb{Q}$; maximal among orders), let $N$ be a nonzero natural number, $m \geq 3$, and $S$ a commutative ring in which both $N$ and $m$ are units. Let $u = (E,\,\mathrm{full\ level})$ be an object of `FakeEllipticCurve.WithFullLevel Λ 1 m S`, that is, a fake elliptic curve $E$ over $S$ with $\Lambda$-action and trivial $\Gamma_0$-parameter together with a level-$m$ structure: a section $P$ of $E.f$ killed by $m$ whose $\Lambda$-orbit exhausts the $m$-torsion at every algebraically closed geometric point and whose annihilator in $\Lambda$ is $m\Lambda$. The assertion is that there exist a scheme $Z$ and a finite étale morphism $\zeta : Z \to \operatorname{Spec} S$, together with a rule $\mathrm{ptZ}$ which assigns, to every commutative ring $T$, ring homomorphism $\varphi : S \to T$, object $u'$ of `FakeEllipticCurve.WithFullLevel Λ 1 m T` satisfying `WithFullLevel.IsPullback φ u u'` (there is $g : u'.1.A \to u.1.A$ making a pullback square over $\operatorname{Spec}\varphi$, compatible with the relative group laws, with the $\Lambda$-actions, carrying points factoring through the $\Gamma_0$-level of $u'$ into that of $u$, and sending the level-$m$ section of $u'$ to the pullback of that of $u$), and extra level $K : u'.1.\mathrm{ExtraLevel}\ N$ (a closed immersion $\mathrm{lev}_K : K \to u'.1.A$ whose points form a $\Lambda$-stable subgroup killed by $N$, meeting the $\Gamma_0$-level only in the identity, finite flat of finite presentation and of rank $N^2$ over the base, with point group $(\mathbb{Z}/N)^2$ at every algebraically closed geometric point where $N \neq 0$), a morphism $\operatorname{Spec} T \to Z$ whose composite with $\zeta$ is $\operatorname{Spec}\varphi$. Four properties are required: $\mathrm{ptZ}$ depends on $K$ only through the predicate "a point of $u'.1.f$ factors through $\mathrm{lev}_K$"; for $\psi : T \to T'$, pullbacks $u'$ of $u$ along $\varphi$ and $u''$ of $u$ along $\psi \circ \varphi$, extra levels $K'$ on $u'$ and $K''$ on $u''$, and a single morphism $g : u''.1.A \to u'.1.A$ witnessing `IsPullbackVia ψ u'.1 u''.1 g` and carrying the level-$m$ section of $u''$ to $\operatorname{Spec}\psi$ followed by that of $u'$, if every point factoring through $\mathrm{lev}_{K''}$ has its image under $g$ factoring through $\mathrm{lev}_{K'}$, then the morphism attached to $(T', \psi \circ \varphi, u'', K'')$ is $\operatorname{Spec}\psi$ followed by the one attached to $(T, \varphi, u', K')$; every morphism $\operatorname{Spec} T \to Z$ over $\operatorname{Spec}\varphi$ is $\mathrm{ptZ}$ of some extra level; and $\mathrm{ptZ}$ separates extra levels with different point predicates.
--
--   This is the representability of $\Gamma_0(N)$-structures (extra levels of order $N$) on a rigidified fake elliptic curve by a finite étale cover of the affine base, the full level-$m$ structure with $m \geq 3$ serving to rigidify the curve so that a rule keyed on arbitrary pullbacks $u'$ is well defined. It is used in the construction of the fine moduli scheme for fake elliptic curves with $\Gamma_0(N)$-level, in [`CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuli_finite_etale_of_isUnit`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuli_finite_etale_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_finite_etale_represents_extraLevel.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_finite_etale_represents_extraLevel
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N]
    (m : ℕ) (hm : 3 ≤ m) (S : Type) [CommRing S] (hN : IsUnit ((N : ℕ) : S)) (hm' : IsUnit ((m : ℕ) : S))
    (u : FakeEllipticCurve.WithFullLevel Λ 1 m S) :
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
              FactorsThrough K.levK P ↔ FactorsThrough K'.levK P) := by sorry
