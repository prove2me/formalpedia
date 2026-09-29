-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_factorsThrough_lev_nsmulPt_eq_one_eq_sq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.natCard_factorsThrough_lev_nsmulPt_eq_one_eq_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/a1881559-9036-556e-97c8-cf2db89cf274
-- title:
--   d-torsion in the level subgroup has d² geometric points
-- statement:
--   Let $a,b$ be rational numbers, let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, let $N$ be a natural number, let $L$ be a commutative ring and let $E$ be a fake elliptic curve of level datum $(\Lambda,N)$ over $L$, i.e. a structure consisting of a scheme $E.A$ with a structure morphism $E.f : E.A \to \operatorname{Spec} L$, a commutative relative group law $E.L$ on the functor of points of $E.f$ (a functorial multiplication, unit and inverse on the sets $\{\varphi : T \to E.A \mid \varphi \text{ followed by } E.f = t\}$), the abelian-scheme property bundle (smooth, proper, connected fibres, admitting a relative group law) for $E.f$, two-dimensional fibres, an action of $\Lambda$ by endomorphisms over $L$ with the stated additivity, multiplicativity and trace conditions, and further data including a morphism $E.\mathrm{lev}$ from an auxiliary scheme $E.C$ to $E.A$. Let $k$ be an algebraically closed field, let $sk : L \to k$ be a ring homomorphism, giving the geometric point $\operatorname{Spec} k \to \operatorname{Spec} L$, assume $N \neq 0$ in $k$, and let $d$ be a natural number dividing $N$. Then the number of morphisms $P : \operatorname{Spec} k \to E.A$ over that geometric point which factor through $E.\mathrm{lev}$ (that is, $P$ is $P_0$ followed by $E.\mathrm{lev}$ for some $P_0 : \operatorname{Spec} k \to E.C$) and satisfy $d\cdot P = 0$, where $d\cdot P$ is the $d$-fold iterate of the group law applied to $P$ starting from the unit, equals $d^2$.
--
--   This is the count of $d$-torsion in the level-$N$ subgroup of a fake elliptic curve at a geometric point of residue characteristic not dividing $N$, the analogue for quaternionic (Shimura-curve) moduli of the statement that the $d$-torsion of $(\mathbb{Z}/N)^2$ has $d^2$ elements. It feeds the corresponding torsion count on a descended level datum and the rigidity argument showing that a section killed by the level structure and the relevant endomorphisms is trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_factorsThrough_lev_nsmulPt_eq_one_eq_sq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.natCard_factorsThrough_lev_nsmulPt_eq_one_eq_sq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {L : Type u} [CommRing L] (E : FakeEllipticCurve Λ N L)
    (k : Type u) [Field k] [IsAlgClosed k] (sk : L →+* k) (hN : (N : k) ≠ 0) (d : ℕ) (hd : d ∣ N) :
    Nat.card {P : SchemeHomOver (geomPoint k sk) E.f //
      FactorsThrough E.lev P ∧ nsmulPt E.L (geomPoint k sk) d P = E.L.one (geomPoint k sk)} = d ^ 2 := by sorry
