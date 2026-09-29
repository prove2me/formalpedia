-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_P_eq_pushPt_act_and_isTwist
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_P_eq_pushPt_act_and_isTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/fbfccf9a-ff31-5ef9-9fd9-abd32030809b
-- title:
--   Twisting a full level structure by a unit mod mΛ
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ which is an order in the sense of `IsOrder`: it contains $1$, is closed under multiplication, spans the quaternion algebra over $\mathbb{Q}$, and is finitely generated. Let $N,m$ be natural numbers, $S$ a commutative ring, $E$ a fake elliptic curve over $S$ with $\Lambda$-action and level datum of level $N$ (a `FakeEllipticCurve Λ N S`, with structure morphism $f : A \to \operatorname{Spec} S$, relative group law $L$, and endomorphisms $\mathrm{act}\,x$ over $S$ for $x \in \Lambda$), and let $P$ be a full level-$m$ structure on $E$: a section of $f$ over $\operatorname{Spec} S$ which is killed by $m$ for $L$, whose translates under $\Lambda$ exhaust the $m$-torsion sections at every geometric point $\operatorname{Spec} k \to \operatorname{Spec} S$ with $k$ algebraically closed, and whose annihilator at every such geometric point is exactly $m\Lambda$. Let $c,d \in \Lambda$ satisfy $cd - 1 \in m\Lambda$ and $dc - 1 \in m\Lambda$ (each written as $m \cdot y$ for some $y \in \Lambda$). Then there is a full level-$m$ structure $P'$ on $E$ whose underlying section is the image of that of $P$ under $\mathrm{act}\,c$, and such that $(E,P')$ is a twist of $(E,P)$ by $c$ in the sense of `WithFullLevel.IsTwist`: there is an isomorphism $e$ of $A$ with itself over $\operatorname{Spec} S$ which is a homomorphism for the group law, commutes with every $\mathrm{act}\,x$, preserves the property of a point factoring through the level morphism $\mathrm{lev}$ in both directions, and carries the $c$-translate of the section of $P$ to the section of $P'$.
--
--   This is the existence half of the statement that a unit of $\Lambda/m\Lambda$ acts on full level-$m$ structures on a fake elliptic curve by re-choosing the generator, the twisting operation underlying the $(\Lambda/m\Lambda)^\times$-action on the fine moduli problem. It is used in the analysis of level-structure transport and of the labelling of families of fake elliptic curves over algebraically closed fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_P_eq_pushPt_act_and_isTwist.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_P_eq_pushPt_act_and_isTwist
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N m : ℕ}
    {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S) (P : E.FullLevel m) (c d : ↥Λ)
    (hcd : ∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    (hdc : ∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) :
    ∃ P' : E.FullLevel m, P'.P = pushPt (E.act c) (E.act_over c) P.P ∧
      FakeEllipticCurve.WithFullLevel.IsTwist c (⟨E, P⟩ : FakeEllipticCurve.WithFullLevel Λ N m S) ⟨E, P'⟩ := by sorry
