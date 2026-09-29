-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_lev_and_nsmulPt_eq_one_of_dvd
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_lev_and_nsmulPt_eq_one_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/9a6fb589-1931-5dbb-84c0-0b2c9cebead4
-- title:
--   n-torsion of the level structure on a geometric fibre
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $M$, a commutative ring $S$ and a fake elliptic curve $E$ of level $M$ over $S$ with $\Lambda$-action, i.e. a structure providing a scheme $E.A$ with a morphism $E.f : E.A \to \operatorname{Spec} S$, a commutative relative group law $E.L$ on $E.f$ whose fibres are two-dimensional, an action of $\Lambda$ by endomorphisms over $S$ compatible with the group law and satisfying the trace condition, and a further scheme $E.C$ with a morphism $E.\mathrm{lev} : E.C \to E.A$. Let $n$ be a natural number dividing $M$, let $k$ be an algebraically closed field, let $sk : S \to k$ be a ring homomorphism, giving the geometric point $\operatorname{Spec} k \to \operatorname{Spec} S$ obtained by applying $\operatorname{Spec}$ to $sk$, and assume the image of $M$ in $k$ is nonzero. Then there is a bijection $e$ from $\mathbb{Z}/n \times \mathbb{Z}/n$ onto the set of those morphisms $P : \operatorname{Spec} k \to E.A$ with $P$ followed by $E.f$ equal to the geometric point, such that $P$ factors as some $P_0 : \operatorname{Spec} k \to E.C$ followed by $E.\mathrm{lev}$ and such that the $n$-fold iterate of $P$ under $E.L$ (defined recursively by $0 \mapsto$ the unit section and $m+1 \mapsto E.L.\mathrm{mul}$ of the $m$-fold iterate with $P$) equals the unit section at the geometric point; moreover $e$ is additive, $e(x+y) = E.L.\mathrm{mul}(e\,x, e\,y)$ for all $x,y$.
--
--   This identifies the $n$-torsion of the level structure on a geometric fibre of a fake elliptic curve with $(\mathbb{Z}/n)^2$, for any divisor $n$ of $M$ with $M$ invertible at the geometric point; no invertibility in $S$ and no coprimality are required. It is used in the constructions of a closed immersion of the $n$-torsion level subscheme and of the curve with extra level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_lev_and_nsmulPt_eq_one_of_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_lev_and_nsmulPt_eq_one_of_dvd
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {M : ℕ}
    (S : Type) [CommRing S] (E : FakeEllipticCurve Λ M S) (n : ℕ) (hn : n ∣ M)
    (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (hk : (M : k) ≠ 0) :
    ∃ e : ZMod n × ZMod n ≃
        {P : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough E.lev P ∧ nsmulPt E.L (geomPoint k sk) n P = E.L.one (geomPoint k sk)},
      ∀ x y : ZMod n × ZMod n,
        (e (x + y) : SchemeHomOver (geomPoint k sk) E.f) = E.L.mul (geomPoint k sk) (e x) (e y) := by sorry
