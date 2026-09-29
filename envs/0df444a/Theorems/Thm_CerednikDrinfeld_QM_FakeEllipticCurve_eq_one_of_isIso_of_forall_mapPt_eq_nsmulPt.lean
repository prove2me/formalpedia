-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_one_of_isIso_of_forall_mapPt_eq_nsmulPt
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.eq_one_of_isIso_of_forall_mapPt_eq_nsmulPt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/fe039986-e1a2-5e81-93e3-c6f92d800b85
-- title:
--   Scalar automorphism ±[k] of a fake elliptic curve forces k=1
-- statement:
--   Fix primes $q,q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is a maximal order, i.e. an order (containing $1$, multiplicatively closed, $\mathbb{Q}$-spanning the algebra, finitely generated) with no strictly larger order above it, let $N$ be a nonzero natural number, and let $E$ be a `FakeEllipticCurve` for $\Lambda$ of level $N$ over $\overline{\mathbb{Q}}$, with total space $E.A$, structure morphism $E.f$ to $\operatorname{Spec}\overline{\mathbb{Q}}$ and relative group law $E.L$. Let $\varphi : E.A \to E.A$ be an isomorphism over $\overline{\mathbb{Q}}$, so $\varphi$ followed by $E.f$ equals $E.f$, and let $k$ be a natural number. Assume that on points $\varphi$ is $[k]$ or $[-k]$: for all schemes $T$, all $t : T \to \operatorname{Spec}\overline{\mathbb{Q}}$ and all $P : T \to E.A$ over $t$, the composite of $P$ with $\varphi$ equals the $k$-fold $E.L$-sum of $P$ (defined recursively, with value the identity section for $k=0$), respectively its $E.L$-inverse. Then $k = 1$.
--
--   This is the bookkeeping step ruling out $k\neq 1$ in the study of automorphisms of a fake elliptic curve (a QM abelian surface) that act as scalar multiplications on points, the analogue for elliptic curves being that $[k]$ is an automorphism only for $k=1$ (up to sign). It feeds the finiteness statement [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_finset_forall_not_iso_forall_hom_eq_id_or_mapPt_eq_inv`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_finset_forall_not_iso_forall_hom_eq_id_or_mapPt_eq_inv) about rigidity of such automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_one_of_isIso_of_forall_mapPt_eq_nsmulPt.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.eq_one_of_isIso_of_forall_mapPt_eq_nsmulPt
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N]
    (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f) [IsIso φ] (k : ℕ)
    (h : (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
            mapPt φ hφ P = nsmulPt E.L t k P) ∨
         (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
            mapPt φ hφ P = E.L.inv t (nsmulPt E.L t k P))) :
    k = 1 := by sorry
