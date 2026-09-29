-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_eq_pushPt_act_of_sub_eq_smul_of_nsmulPt_eq_one
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_eq_pushPt_act_of_sub_eq_smul_of_nsmulPt_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/1bae6e1f-e4ce-504b-9f1d-7c3bae391ba5
-- title:
--   Elements of Λ congruent mod mΛ agree on m-torsion
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a commutative ring $S$, and let $E$ be a `FakeEllipticCurve Λ N S`: this bundles a scheme `E.A` with a structure morphism `E.f` to $\operatorname{Spec} S$, a relative group law `E.L` on the functor of points over $\operatorname{Spec} S$ which is commutative, the property bundle asserting `E.f` smooth, proper, with connected fibres and admitting a group law, fibres of topological Krull dimension $2$, together with an action `E.act` of $\Lambda$ by endomorphisms of `E.A` over $\operatorname{Spec} S$ (`E.act_over`) that is additive in the parameter, multiplicative in the contravariant sense $\mathrm{act}(xy) = \mathrm{act}(y)$ followed by $\mathrm{act}(x)$, sends $1$ to the identity, is a homomorphism for the group law, and satisfies a trace condition on tangent spaces at geometric points, plus the further data of the structure. Assume $1 \in \Lambda$. Let $m$ be a natural number, $T$ a scheme with a morphism $t : T \to \operatorname{Spec} S$, and $P$ a point of `E.A` over $t$, i.e. a morphism $T \to$ `E.A` whose composite with `E.f` is $t$. Assume the $m$-fold multiple of $P$ for `E.L`, defined by iterating `E.L.mul` from `E.L.one t`, is the unit point `E.L.one t`. Let $c, c' \in \Lambda$ be such that $c - c' = m \cdot y$ for some $y \in \Lambda$. Then $P$ followed by `E.act c` and $P$ followed by `E.act c'` agree as points over $t$.
--
--   The statement is the standard fact that the action of a quaternionic multiplication ring on the $m$-torsion of a fake elliptic curve factors through $\Lambda/m\Lambda$; it is what makes twisting a full level-$m$ structure by an element of $\Lambda$ depend only on its class modulo $m$. It is used in the rigidification of fake elliptic curves, in the construction of isomorphisms compatible with level structures at a geometric point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_eq_pushPt_act_of_sub_eq_smul_of_nsmulPt_eq_one.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_eq_pushPt_act_of_sub_eq_smul_of_nsmulPt_eq_one
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (m : ℕ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f)
    (hP : nsmulPt E.L t m P = E.L.one t)
    (c c' : ↥Λ) (hcc' : ∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) - (c' : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])) :
    pushPt (E.act c) (E.act_over c) P = pushPt (E.act c') (E.act_over c') P := by sorry
