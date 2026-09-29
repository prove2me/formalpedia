-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAtkinLehnerQuotientVia_comp_eq_of_isPullbackVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isAtkinLehnerQuotientVia_comp_eq_of_isPullbackVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/46fc08dc-1d34-54ee-a57e-768c9d7cdec4
-- title:
--   Base change of Atkin–Lehner quotients of fake elliptic curves
-- statement:
--   Fix $r, N \in \mathbb{N}$, rationals $a, b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, commutative rings $S$, $S'$ and a ring homomorphism $\varphi : S \to S'$. Let $E, E'$ be fake elliptic curves of type $(\Lambda, N)$ over $S$, and let $q : E.A \to E'.A$ and $q' : E'.A \to E.A$ be morphisms over $\mathrm{Spec}\,S$ (that is, $q$ followed by $E'.f$ equals $E.f$, and $q'$ followed by $E.f$ equals $E'.f$). Assume `IsAtkinLehnerQuotientVia` holds for $r, E, E', q, q'$: for every scheme $T$ and every $t : T \to \mathrm{Spec}\,S$, composition with $q$ (resp. $q'$) is additive for the relative group laws on $T$-points over $t$; $E.\mathrm{act}\,x$ followed by $q$ equals $q$ followed by $E'.\mathrm{act}\,x$, and $E'.\mathrm{act}\,x$ followed by $q'$ equals $q'$ followed by $E.\mathrm{act}\,x$, for all $x \in \Lambda$; if the image of $r$ in $\mathbb{H}[\mathbb{Q},a,b]$ lies in $\Lambda$ then $q \,$ followed by $q'$ is $E.\mathrm{act}\,r$ and $q'$ followed by $q$ is $E'.\mathrm{act}\,r$; for every $T$-point $P$ of $E$ over $t$, the composite $P$ followed by $q$ is the identity section of $E'$ if and only if for every $m \in \Lambda$ and $n \in \mathbb{Z}$ with $m\,\overline{m} = rn$ the composite $P$ followed by $E.\mathrm{act}\,m$ is the identity section of $E$; and $q$ carries points factoring through $E.\mathrm{lev}$ to points factoring through $E'.\mathrm{lev}$. Let further $E_1$, $E_1'$ be fake elliptic curves of type $(\Lambda,N)$ over $S'$ together with $g : E_1.A \to E.A$ and $g' : E_1'.A \to E'.A$ satisfying `FakeEllipticCurve.IsPullbackVia` for $\varphi$: the square formed by $g$, $E_1.f$, $E.f$ and $\mathrm{Spec}\,\varphi$ is cartesian, composition with $g$ is compatible with the two group laws on points (over $t'$ and over $t'$ followed by $\mathrm{Spec}\,\varphi$), $E_1.\mathrm{act}\,x$ followed by $g$ equals $g$ followed by $E.\mathrm{act}\,x$ for all $x \in \Lambda$, and every point of $E_1$ factoring through $E_1.\mathrm{lev}$ becomes, after composing with $g$, a map factoring through $E.\mathrm{lev}$; likewise for $g'$, $E'$, $E_1'$. The conclusion asserts the existence of morphisms $q_1 : E_1.A \to E_1'.A$ and $q_1' : E_1'.A \to E_1.A$ over $\mathrm{Spec}\,S'$ such that $q_1$ followed by $g'$ equals $g$ followed by $q$, $q_1'$ followed by $g$ equals $g'$ followed by $q'$, and $(q_1, q_1')$ again satisfies `IsAtkinLehnerQuotientVia` at the same $r$ for $E_1$, $E_1'$.
--
--   This is the base-change stability of Atkin–Lehner quotient data for fake elliptic curves: an Atkin–Lehner pair at $r$ over $S$ induces, compatibly with the comparison morphisms of the cartesian squares, an Atkin–Lehner pair at $r$ on any pullback along $\varphi : S \to S'$. It is used in the rigidification part of the Čerednik–Drinfeld comparison, where the Atkin–Lehner operator must be transported to local models over the rings occurring there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAtkinLehnerQuotientVia_comp_eq_of_isPullbackVia.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isAtkinLehnerQuotientVia_comp_eq_of_isPullbackVia
    {r : ℕ} {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E E' : FakeEllipticCurve Λ N S)
    (q : E.A ⟶ E'.A) (hq : q ≫ E'.f = E.f) (q' : E'.A ⟶ E.A) (hq' : q' ≫ E.f = E'.f)
    (hAL : FakeEllipticCurve.IsAtkinLehnerQuotientVia r E E' q hq q' hq')
    (E₁ : FakeEllipticCurve Λ N S') (g : E₁.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia φ E E₁ g)
    (E₁' : FakeEllipticCurve Λ N S') (g' : E₁'.A ⟶ E'.A) (hg' : FakeEllipticCurve.IsPullbackVia φ E' E₁' g') :
    ∃ (q₁ : E₁.A ⟶ E₁'.A) (hq₁ : q₁ ≫ E₁'.f = E₁.f) (q₁' : E₁'.A ⟶ E₁.A) (hq₁' : q₁' ≫ E₁.f = E₁'.f),
      q₁ ≫ g' = g ≫ q ∧ q₁' ≫ g = g' ≫ q' ∧
      FakeEllipticCurve.IsAtkinLehnerQuotientVia r E₁ E₁' q₁ hq₁ q₁' hq₁' := by sorry
