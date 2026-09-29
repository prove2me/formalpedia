-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_isPullback_levelIff_of_isUnit_of_isIndefiniteRamifiedExactlyAt
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_isPullback_levelIff_of_isUnit_of_isIndefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/75df064e-f9a7-5cc2-8396-2007b0f9f30e
-- title:
--   Noetherian descent of full-level fake elliptic curves
-- statement:
--   Fix $a,b\in\mathbb{Q}$ and primes $q,q'$, and assume `IsIndefiniteRamifiedExactlyAt a b q q'`: the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $q$ or $q'$ lies in $v$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order (an order maximal among orders for inclusion), let $N$ be a nonzero natural number, $m$ a natural number, $L$ a commutative ring, $u=(E,P)$ a fake elliptic curve over $L$ with $\Lambda$-action and level-$N$ data together with a full level-$m$ structure on $E$, $s\subseteq L$ a finite subset, and suppose $m$ is a unit in $L$. Then there are a finitely generated $\mathbb{Z}$-subalgebra $R\subseteq L$ containing $s$, an object $u_R$ of the same kind over $R$, and a morphism $g:E.A\to u_R.1.A$ making the square formed by $g$, $E.f$, $u_R.1.f$ and $\operatorname{Spec}$ of the inclusion $R\hookrightarrow L$ cartesian, such that: $g$ carries the relative group law of $E$ to that of $u_R$ on $T$-points over any $t':T\to\operatorname{Spec}L$; $E.\mathrm{act}\,x$ followed by $g$ equals $g$ followed by $u_R.1.\mathrm{act}\,x$ for all $x\in\Lambda$; for all such $T$, $t'$ and all $P:T\to E.A$ over $t'$, $P$ factors through $E.\mathrm{lev}$ if and only if $P$ followed by $g$ factors through $u_R.1.\mathrm{lev}$; and $g$ transports the full level-$m$ section of $u$ to the base change of that of $u_R$.
--
--   This is the spreading-out (Noetherian approximation) step for the moduli problem of fake elliptic curves with level data and a full level-$m$ structure: any such object over an arbitrary commutative ring descends, compatibly with the group law, the quaternionic action, the level subscheme and the distinguished section, to a finitely generated $\mathbb{Z}$-subalgebra, which may be taken to contain any prescribed finite set of elements. It underlies the treatment of directed colimits of base rings, being cited by the statements producing pullback objects and isomorphisms over a directed colimit when $m$ is invertible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_isPullback_levelIff_of_isUnit_of_isIndefiniteRamifiedExactlyAt.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_isPullback_levelIff_of_isUnit_of_isIndefiniteRamifiedExactlyAt
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] (m : ℕ)
    (L : Type) [CommRing L] (u : FakeEllipticCurve.WithFullLevel Λ N m L) (s : Finset L)
    (hm : IsUnit ((m : ℕ) : L)) :
    ∃ (R : Subalgebra ℤ L) (_ : R.FG) (_ : (↑s : Set L) ⊆ R) (uR : FakeEllipticCurve.WithFullLevel Λ N m ↥R) (g : u.1.A ⟶ uR.1.A)
      (hg : CategoryTheory.IsPullback g u.1.f uR.1.f (Spec.map (CommRingCat.ofHom R.val.toRingHom))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' u.1.f),
        (u.1.L.mul t' P Q).1 ≫ g =
          (uR.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, u.1.act x ≫ g = g ≫ uR.1.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' u.1.f),
        FactorsThrough u.1.lev P → ∃ P₀ : T ⟶ uR.1.C, P₀ ≫ uR.1.lev = P.1 ≫ g) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' u.1.f),
        (∃ P₀ : T ⟶ uR.1.C, P₀ ≫ uR.1.lev = P.1 ≫ g) → FactorsThrough u.1.lev P) ∧
      (u.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ (uR.2.P).1 := by sorry
