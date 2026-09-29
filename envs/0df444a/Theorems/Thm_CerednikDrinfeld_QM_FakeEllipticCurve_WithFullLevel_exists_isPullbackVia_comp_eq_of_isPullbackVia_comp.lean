-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullbackVia_comp_eq_of_isPullbackVia_comp
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullbackVia_comp_eq_of_isPullbackVia_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/5339f26d-1d23-50e1-bc2b-bf2fcc10d6d6
-- title:
--   Factoring a base change through a pullback of fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$ and naturals $N,m,\ell$; let $\varphi:S\to S'$ and $\psi:S'\to S''$ be homomorphisms of commutative rings, and let $u,u_1,u''$ be pairs consisting of a fake elliptic curve with $\Lambda$-action and level-$N$ structure over $S$, $S'$, $S''$ respectively together with a full level-$m$ structure, with $Cu,Cu_1,Cu''$ extra level-$\ell$ structures on the underlying curves (a closed immersion $levK$ of a scheme $K$ into the abelian scheme, stable under the group law, inversion and $\Lambda$, killed by $\ell$, disjoint from $lev$, finite flat of fibre rank $\ell^2$ with geometric fibres $\mathbb{Z}/\ell\times\mathbb{Z}/\ell$). Given $g_1:u_1.A\to u.A$ and $g:u''.A\to u.A$, assume: `FakeEllipticCurve.IsPullbackVia` holds for $\varphi$ and $g_1$, i.e. the square formed by $g_1$, the two structure morphisms and $\mathrm{Spec}\,\varphi$ is cartesian, $g_1$ carries products of $T$-points to products of their images, commutes with each $act\,x$ for $x\in\Lambda$, and takes points factoring through $u_1.lev$ to points whose composite with $g_1$ factors through $u.lev$; the level-$m$ point of $u_1$ composed with $g_1$ equals $\mathrm{Spec}\,\varphi$ followed by that of $u$; $u_1.lev$ is the full preimage, in that a point $P$ factors through $u_1.lev$ as soon as $P\circ g_1$ factors through $u.lev$; $Cu_1.levK$ is the full preimage of $Cu.levK$ along $g_1$, both directions; the same pullback property for $\psi\circ\varphi$ and $g$, with the matching level-$m$ compatibility, and one direction of the extra-level compatibility for $g$ (points through $Cu''.levK$ go into $Cu.levK$). Then there is $g':u''.A\to u_1.A$ with $g'$ followed by $g_1$ equal to $g$, satisfying `IsPullbackVia` for $\psi$, compatible with the level-$m$ points over $\mathrm{Spec}\,\psi$, and sending points factoring through $Cu''.levK$ to points whose composite with $g'$ factors through $Cu_1.levK$. No uniqueness of $g'$ is asserted.
--
--   This is the cancellation step for base changes of tuples (fake elliptic curve, full level-$m$ structure, extra level-$\ell$ structure): since $u_1$ is the base change of $u$ along $\varphi$, a base change along $\psi\circ\varphi$ factors through it along $\psi$. It feeds the directed-colimit assembly of such tuples over a filtered system of base rings, being used by [`CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isoTVia_of_isoTVia_of_directed_colimit_of_isUnit`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isoTVia_of_isoTVia_of_directed_colimit_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullbackVia_comp_eq_of_isPullbackVia_comp.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuliT

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullbackVia_comp_eq_of_isPullbackVia_comp
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m ℓ : ℕ}
    {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) (u₁ : FakeEllipticCurve.WithFullLevel Λ N m S')
    (u'' : FakeEllipticCurve.WithFullLevel Λ N m S'')
    (Cu : u.1.ExtraLevel ℓ) (Cu₁ : u₁.1.ExtraLevel ℓ) (Cu'' : u''.1.ExtraLevel ℓ)
    (g₁ : u₁.1.A ⟶ u.1.A) (g : u''.1.A ⟶ u.1.A)
    (h₁ : FakeEllipticCurve.IsPullbackVia φ u.1 u₁.1 g₁) (h₁P : (u₁.2.P).1 ≫ g₁ = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1)
    (h₁L : (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u₁.1.f),
          (∃ P₀ : T₀ ⟶ u.1.C, P₀ ≫ u.1.lev = P.1 ≫ g₁) → FactorsThrough u₁.1.lev P))
    (h₁C : (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u₁.1.f),
          FactorsThrough Cu₁.levK P ↔ ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ g₁))
    (h : FakeEllipticCurve.IsPullbackVia (ψ.comp φ) u.1 u''.1 g) (hP : (u''.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (ψ.comp φ)) ≫ (u.2.P).1)
    (hC : (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S'')) (P : SchemeHomOver t' u''.1.f),
          FactorsThrough Cu''.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ g)) :
    ∃ g' : u''.1.A ⟶ u₁.1.A, g' ≫ g₁ = g ∧
      FakeEllipticCurve.IsPullbackVia ψ u₁.1 u''.1 g' ∧ (u''.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom ψ) ≫ (u₁.2.P).1 ∧
      (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S'')) (P : SchemeHomOver t' u''.1.f),
          FactorsThrough Cu''.levK P → ∃ P₀ : T₀ ⟶ Cu₁.K, P₀ ≫ Cu₁.levK = P.1 ≫ g') := by sorry
