-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_eq_pushPt_act_and_isTwist_of_mul_sub_one_eq_smul
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_eq_pushPt_act_and_isTwist_of_mul_sub_one_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/38d379ce-5779-554b-bf11-73543c4867b0
-- title:
--   Twisting a full level-m structure by a unit mod mΛ
-- statement:
--   Let $a,b\in\mathbb Q$ and let $\Lambda$ be a $\mathbb Z$-submodule of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ which is an order in the sense of `IsOrder`: $1\in\Lambda$, $\Lambda$ is closed under multiplication, its $\mathbb Q$-span is everything, and it is finitely generated. Fix $N,m\in\mathbb N$ and a commutative ring $S$, and let $E$ be a `FakeEllipticCurve Λ N S`, i.e. a scheme $A$ with a structure morphism $f\colon A\to\operatorname{Spec}S$ carrying a commutative relative group law $L$ on its functor of points, the stated abelian-scheme property bundle and two-dimensional fibres, an action $x\mapsto \mathrm{act}(x)$ of $\Lambda$ by endomorphisms over $S$ which is additive and multiplicative on points and satisfies the trace condition, together with its level datum $\mathrm{lev}$. Let $P$ be a full level-$m$ structure on $E$: a section $P.P$ of $f$ over $\mathrm{id}_{\operatorname{Spec}S}$ with $m\cdot P.P$ the identity section, such that for every algebraically closed field $k$ and every ring homomorphism $sk\colon S\to k$ each $m$-torsion point over the associated geometric point is $\mathrm{act}(x)$ applied to the restriction of $P.P$ for some $x\in\Lambda$, and $\mathrm{act}(x)$ applied to that restriction is the identity point exactly when $x\in m\Lambda$. Let $c,d\in\Lambda$ be such that $cd-1$ and $dc-1$ both lie in $m\Lambda$, i.e. each equals $m\cdot y$ for some $y\in\Lambda$. Then there is a full level-$m$ structure $P'$ on the same $E$ whose section is $P.P$ composed with $\mathrm{act}(c)$, and $\langle E,P'\rangle$ is a twist of $\langle E,P\rangle$ by $c$ in the sense of `WithFullLevel.IsTwist`: there is an isomorphism $e$ of $A$ with itself over $\operatorname{Spec}S$ which is compatible with the group law on points, commutes with $\mathrm{act}(x)$ for every $x\in\Lambda$, preserves the property of a point factoring through $\mathrm{lev}$ in both directions, and carries $\mathrm{act}(c)$ applied to $P.P$ to $P'.P$.
--
--   This is the closure of full level-$m$ structures under twisting by an element of $\Lambda$ invertible modulo $m\Lambda$, the first step in constructing the level-twisting action of $(\Lambda/m\Lambda)^{\times}$ on the moduli problem of fake elliptic curves with full level-$m$ structure. It is used in the construction of the twisting action on a fine moduli scheme and in the lifting of that action to extra level structures, and in the statement about flat surjective covers by full level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_eq_pushPt_act_and_isTwist_of_mul_sub_one_eq_smul.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_eq_pushPt_act_and_isTwist_of_mul_sub_one_eq_smul
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N : ℕ}
    {S : Type u} [CommRing S] {m : ℕ} (E : FakeEllipticCurve Λ N S) (P : E.FullLevel m) (c d : ↥Λ)
    (hcd : ∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    (hdc : ∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) :
    ∃ P' : E.FullLevel m, P'.P = pushPt (E.act c) (E.act_over c) P.P ∧
      FakeEllipticCurve.WithFullLevel.IsTwist c (⟨E, P⟩ : FakeEllipticCurve.WithFullLevel Λ N m S) ⟨E, P'⟩ := by sorry
