-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_extraLevel_isPullbackVia_forall_factorsThrough_iff
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_extraLevel_isPullbackVia_forall_factorsThrough_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/7d1cf901-0673-5a68-93e8-a5433fc08fb0
-- title:
--   Base change of a fake elliptic curve with full and extra level
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and naturals $N$, $m$, $\ell$; let $\varphi : S \to S'$ be a homomorphism of commutative rings, let $u = (E,P)$ consist of a fake elliptic curve $E$ over $S$ of level $N$ with $\Lambda$-action together with a full level-$m$ structure $P$ (a section of $E.f$ over $\operatorname{Spec} S$, killed by $m$, whose $\Lambda$-translates exhaust the $m$-torsion at every geometric point and whose annihilator in $\Lambda$ is $m\Lambda$), and let $Cu$ be an extra level structure of level $\ell$ on $E$, given by a closed immersion $Cu.levK : Cu.K \to E.A$ with the stated subgroup, $\ell$-torsion, $\Lambda$-stability, disjointness from $E.lev$, finite flat rank $\ell^2$ and fibrewise $(\mathbb{Z}/\ell)^2$ properties. The assertion is the existence of a fake elliptic curve with full level-$m$ structure $u' = (E',P')$ over $S'$, an extra level structure $Cu'$ of level $\ell$ on $E'$, and a single morphism $g : E'.A \to E.A$ such that: $g$ exhibits $E'$ as the base change of $E$ along $\varphi$ in the sense of `FakeEllipticCurve.IsPullbackVia`, i.e. the square formed by $g$, $E'.f$, $E.f$ and $\operatorname{Spec}\varphi$ is a pullback, $g$ is compatible with the relative group laws on $T$-points, satisfies $E'.act\,x$ followed by $g$ equals $g$ followed by $E.act\,x$ for all $x \in \Lambda$, and carries any $T$-point factoring through $E'.lev$ to one factoring through $E.lev$; $P'$ followed by $g$ equals $\operatorname{Spec}\varphi$ followed by $P$; conversely, for every scheme $T_0$, every $t' : T_0 \to \operatorname{Spec} S'$ and every $T_0$-point $P$ of $E'$ over $t'$, if $P$ followed by $g$ factors through $E.lev$ then $P$ factors through $E'.lev$; and $P$ factors through $Cu'.levK$ if and only if $P$ followed by $g$ factors through $Cu.levK$.
--
--   This is the base-change statement for the moduli problem of fake elliptic curves with a full level-$m$ structure and an auxiliary level-$\ell$ structure, in the form needed for descent arguments: the base-changed object comes with one comparison morphism $g$ over $\operatorname{Spec}\varphi$, and both the level-$N$ and the extra level subschemes of $E'$ are exactly the preimages under $g$ of those of $E$. It feeds the limit and uniqueness arguments for the fine moduli functor, in particular the reduction to finitely generated subalgebras and the colimit comparison along directed systems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_extraLevel_isPullbackVia_forall_factorsThrough_iff.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuliT

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_extraLevel_isPullbackVia_forall_factorsThrough_iff
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m ℓ : ℕ}
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) (Cu : u.1.ExtraLevel ℓ) :
    ∃ (u' : FakeEllipticCurve.WithFullLevel Λ N m S') (Cu' : u'.1.ExtraLevel ℓ) (g : u'.1.A ⟶ u.1.A),
      FakeEllipticCurve.IsPullbackVia φ u.1 u'.1 g ∧
      (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1 ∧
      (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
          (∃ P₀ : T₀ ⟶ u.1.C, P₀ ≫ u.1.lev = P.1 ≫ g) → FactorsThrough u'.1.lev P) ∧
      (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
          FactorsThrough Cu'.levK P ↔ ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ g) := by sorry
