-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_finset_forall_not_iso_not_exists_mapPt_mapPt_mul_zpow_eq_zpow
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_finset_forall_not_iso_not_exists_mapPt_mapPt_mul_zpow_eq_zpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/93c0df13-1eb8-5ae6-a095-7fc9756a57b4
-- title:
--   Finitely many fake elliptic curves with quadratic multiplication
-- statement:
--   Let $q$ and $q'$ be distinct primes and let $a,b\in\mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, let $N$ be a nonzero natural number, and let $t,n$ be integers with $t^2<4n$. The assertion is that there are a natural number $m$ and a family $S:\mathrm{Fin}\,m\to$ `FakeEllipticCurve` $\Lambda\,N\,\overline{\mathbb{Q}}$ — each member consisting of a scheme $A$ over $\operatorname{Spec}\overline{\mathbb{Q}}$ with structure morphism $f$, a commutative relative group law $L$ on $T$-valued points, smoothness, properness, connected fibres, fibres of Krull dimension $2$, an action of $\Lambda$ by $f$-morphisms which is additive and multiplicative and satisfies the trace condition on tangent spaces, together with the level-$N$ datum $C$, `lev` — such that for every such $E$ which is not `FakeEllipticCurve.Iso` to any $S j$ (no isomorphism of the underlying schemes over $\overline{\mathbb{Q}}$ respecting the group law, commuting with the $\Lambda$-action, and preserving factorisation through the level structure), there exists no endomorphism $\varphi:E.A\to E.A$ with $\varphi$ followed by $E.f$ equal to $E.f$ which is additive on $T$-valued points for $E.L$, commutes with $E.\mathrm{act}\,x$ for all $x\in\Lambda$, and satisfies, in the commutative group of $T$-valued points over any $s:T\to\operatorname{Spec}\overline{\mathbb{Q}}$, the relation $\varphi(\varphi P)\cdot P^{\,n}=\varphi(P)^{\,t}$.
--
--   This is the finiteness of CM points of fixed imaginary quadratic type on a quaternionic (fake elliptic) moduli problem: off a finite list of isomorphism classes, no fake elliptic curve of level $N$ over $\overline{\mathbb{Q}}$ carries a $\Lambda$-equivariant endomorphism satisfying $\varphi^2-t\varphi+n=0$ with $t^2<4n$. It feeds the corresponding statement for quasi-inverse endomorphisms expressed through multiplication-by-$n$ maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_finset_forall_not_iso_not_exists_mapPt_mapPt_mul_zpow_eq_zpow.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_finset_forall_not_iso_not_exists_mapPt_mapPt_mul_zpow_eq_zpow
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] (t n : ℤ) (htn : t ^ 2 < 4 * n) :
    ∃ (m : ℕ) (S : Fin m → FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
      ∀ E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ), (∀ j : Fin m, ¬ FakeEllipticCurve.Iso E (S j)) →
        ¬ ∃ (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f),
          (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver s E.f),
              mapPt φ hφ (E.L.mul s P Q) = E.L.mul s (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
          (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E.act x) ∧
          ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver s E.f),
            letI := E.L.pointCommGroup E.comm s
            mapPt φ hφ (mapPt φ hφ P) * P ^ n = mapPt φ hφ P ^ t := by sorry
