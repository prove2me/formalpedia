-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_levelIff
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/7a7ff2fb-0c3f-5ee5-b7bc-7001bbd79842
-- title:
--   Base change of fake elliptic curves with full level-m structure
-- statement:
--   Let $a,b\in\mathbb{Q}$, let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, let $N,m\in\mathbb{N}$, let $S,S'$ be commutative rings and $\varphi : S\to S'$ a ring homomorphism, and let $u=(E,P)$ consist of a fake elliptic curve $E$ for $(\Lambda,N)$ over $S$ together with a full level-$m$ structure on $E$. Then there are data $u'=(E',P')$ of the same kind over $S'$, a morphism $g : E'.A\to E.A$ of schemes, and a proof that the square formed by $g$, $E'.f$, $E.f$ and $\operatorname{Spec}(\varphi)$ is cartesian, such that five conditions hold. First, $g$ is a homomorphism on points: for every scheme $T$, every $t' : T\to\operatorname{Spec} S'$ and all $P,Q : T\to E'.A$ over $t'$, the composite of $E'.L.\mathrm{mul}\,t'\,P\,Q$ with $g$ equals the $E.L$-product, taken over $t'$ followed by $\operatorname{Spec}(\varphi)$, of $P$ followed by $g$ and $Q$ followed by $g$. Secondly, $E'.\mathrm{act}\,x$ followed by $g$ equals $g$ followed by $E.\mathrm{act}\,x$ for every $x\in\Lambda$. Thirdly and fourthly, in both directions: a point $P$ of $E'.A$ over $t'$ factors as $P_0$ followed by $E'.\mathrm{lev}$ for some $P_0 : T\to E'.C$ if and only if there is $P_0 : T\to E.C$ with $P_0$ followed by $E.\mathrm{lev}$ equal to $P$ followed by $g$. Finally, the level-$m$ section is transported: $P'$ followed by $g$ equals $\operatorname{Spec}(\varphi)$ followed by $P$.
--
--   This is the base-change statement for the moduli problem of fake elliptic curves with full level-$m$ structure: the pullback of such data along $\operatorname{Spec}(\varphi)$ exists, with the comparison morphism $g$, the cartesian square and the equivariance, group-law, level and section clauses exposed rather than packaged in `WithFullLevel.IsPullback`, and with the level condition recorded as an equivalence rather than only one implication. It feeds the descent and cancellation lemmas used in the construction of the Čerednik–Drinfeld fine and coarse moduli schemes, notably the comparison of level transports and the passage to finitely generated subalgebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_levelIff.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) :
    ∃ (u' : FakeEllipticCurve.WithFullLevel Λ N m S') (g : u'.1.A ⟶ u.1.A)
      (hg : CategoryTheory.IsPullback g u'.1.f u.1.f (Spec.map (CommRingCat.ofHom φ))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' u'.1.f),
        (u'.1.L.mul t' P Q).1 ≫ g =
          (u.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, u'.1.act x ≫ g = g ≫ u.1.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
        FactorsThrough u'.1.lev P → ∃ P₀ : T ⟶ u.1.C, P₀ ≫ u.1.lev = P.1 ≫ g) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
        (∃ P₀ : T ⟶ u.1.C, P₀ ≫ u.1.lev = P.1 ≫ g) → FactorsThrough u'.1.lev P) ∧
      (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1 := by sorry
