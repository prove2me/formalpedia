-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isTwistVia_refl
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isTwistVia_refl
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/40147efa-0d3a-5316-a7f9-705ab337c4bc
-- title:
--   Twisting a full level structure by a unit modulo m
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is an order in the sense of `IsOrder`: it contains $1$, is closed under multiplication, spans $\mathbb{H}[\mathbb{Q},a,b]$ over $\mathbb{Q}$, and is finitely generated. Fix naturals $N,m$, a commutative ring $S$, and $u=(E,P)$ in `FakeEllipticCurve.WithFullLevel Λ N m S`, that is, a fake elliptic curve $E$ over $S$ for the data $(\Lambda,N)$ together with a full level-$m$ structure $P$ on $E$: a section of $E.f$ over $\operatorname{Spec} S$ killed by $m$ for the relative group law, whose $\Lambda$-translates $x\cdot P$ exhaust the $m$-torsion at every geometric point, and with $x\cdot P$ trivial at geometric points exactly when $x\in m\Lambda$. Let $c,d\in\Lambda$ satisfy $cd-1=m\,y$ and $dc-1=m\,y'$ for some $y,y'\in\Lambda$, so that $c$ is a two-sided unit modulo $m\Lambda$ with inverse $d$. The conclusion asserts the existence of a full level-$m$ structure $P'$ on the same curve $u.1$ such that `IsTwistVia c u ⟨u.1, P'⟩` holds with respect to the identity isomorphism of $u.1.A$: the clauses on compatibility with the group law, with the $\Lambda$-action and with the level-$N$ structure hold for the identity, and the final clause states that $P'$ has underlying section the translate $c\cdot P$ of $P$ by $E.\mathrm{act}\,c$.
--
--   This is the statement that twisting a full level-$m$ structure by an element of $\Lambda$ invertible modulo $m\Lambda$ again yields a full level-$m$ structure, on the unchanged underlying fake elliptic curve and with the identity as twisting isomorphism; it is the witnessed form of the twisting law used in the fine moduli theory of fake elliptic curves with full level structure. It is cited by the lemmas on labels and presentation labels of such curves, where the twist must be recognised as carrying any further structure on the curve along unchanged.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isTwistVia_refl.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isTwistVia_refl
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N m : ℕ} {S : Type} [CommRing S]
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) (c d : ↥Λ)
    (hcd : ∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    (hdc : ∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) :
    ∃ P' : u.1.FullLevel m,
      FakeEllipticCurve.WithFullLevel.IsTwistVia c u ⟨u.1, P'⟩ (Iso.refl u.1.A) (Category.id_comp u.1.f) := by sorry
