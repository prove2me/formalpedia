-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/7e3067fd-7940-5efa-abd9-e968e186cf2c
-- title:
--   Base change of a fake elliptic curve, with cartesian square and level
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, commutative rings $S,S'$ and a ring homomorphism $\varphi : S \to S'$, and let $E$ be a fake elliptic curve over $S$ with $\Lambda$-action and level $N$ in the sense of the project structure `FakeEllipticCurve` (a scheme $E.A$ with a structure morphism $E.f$ to $\operatorname{Spec} S$ carrying a commutative relative group law $E.L$, smooth proper with connected fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over the base satisfying the additivity, multiplicativity and trace conditions, and a level datum $E.\mathrm{lev} : E.C \to E.A$). Then there exist a fake elliptic curve $E'$ over $S'$ of the same kind, a morphism $g : E'.A \to E.A$, and a proof that the square formed by $g$, $E'.f$, $E.f$ and $\operatorname{Spec}\varphi$ is cartesian, such that: (i) $g$ is a homomorphism on points, i.e. for every scheme $T$, every $t' : T \to \operatorname{Spec} S'$ and all $P,Q : T \to E'.A$ over $t'$, the underlying morphism of $E'.L$-product of $P$ and $Q$ followed by $g$ equals the $E.L$-product, over $t'$ followed by $\operatorname{Spec}\varphi$, of $P$ followed by $g$ and $Q$ followed by $g$; (ii) $E'.\mathrm{act}\,x$ followed by $g$ equals $g$ followed by $E.\mathrm{act}\,x$ for every $x \in \Lambda$; (iii) for every such $T,t',P$, the point $P$ factors through $E'.\mathrm{lev}$ if and only if there is $P_0 : T \to E.C$ with $P_0$ followed by $E.\mathrm{lev}$ equal to $P$ followed by $g$ (stated as the two implications).
--
--   This is the existence of the base change along $\varphi$ of a fake elliptic curve (a quaternionic abelian surface with $\Lambda$-action and level-$N$ structure), in a form stronger than the project predicate `IsPullback`: the cartesian square is produced as data together with the comparison morphism $g$, and the level condition is an equivalence rather than only the implication that points of $E'.C$ map into $E.C$. It is the base-change input for the constructions of extra level structures and level isogenies on integral models of Shimura curves in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits NeronModelInfra CerednikDrinfeld.QM
open AlgebraicGeometry

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S) :
    ∃ (E' : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S') (g : E'.A ⟶ E.A)
      (hg : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ))),
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f),
        (E'.L.mul t' P Q).1 ≫ g =
          (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E'.act x ≫ g = g ≫ E.act x) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' E'.f),
        FactorsThrough E'.lev P → ∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ g) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' E'.f),
        (∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ g) → FactorsThrough E'.lev P) := by sorry
