-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_symm_of_isAtkinLehnerQuotientVia_of_not_dvd
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.preservesLevel_symm_of_isAtkinLehnerQuotientVia_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/10856198-d602-590b-b2cf-8ed368db5639
-- title:
--   Dual Atkin–Lehner map preserves level structure for r ∤ N
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ containing the image of every integer, a natural number $N$, a prime $r$ with $r \nmid N$, and a commutative ring $S$. Let $E$ and $E'$ be fake elliptic curves of level data $(\Lambda,N)$ over $S$, i.e. structures consisting of a scheme with a morphism to $\operatorname{Spec} S$, a commutative relative group law on its $T$-points, the abelian-scheme property bundle, two-dimensional fibres, an action `act` of $\Lambda$ by endomorphisms over $S$ satisfying the additivity, multiplicativity and trace axioms, together with a level scheme $C$ and a morphism `lev` to the total space. Let $q : E.A \to E'.A$ and $q' : E'.A \to E.A$ be morphisms over $\operatorname{Spec} S$ ($q$ followed by $E'.f$ equals $E.f$, and $q'$ followed by $E.f$ equals $E'.f$) forming an Atkin–Lehner quotient at $r$: both are homomorphisms for the relative group laws on $T$-points, both commute with the $\Lambda$-actions, whenever the image of $r$ lies in $\Lambda$ the two composites are the actions of $r$ on $E$ and on $E'$ respectively, a $T$-point $P$ of $E$ is killed by $q$ exactly when it is killed by `act m` for all $m \in \Lambda$ and $n \in \mathbb{Z}$ with $m\,\overline{m} = rn$, and $q$ sends $T$-points factoring through $E.\mathrm{lev}$ to $T$-points factoring through $E'.\mathrm{lev}$. The conclusion is the symmetric statement for $q'$: for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and every $T$-point $P$ of $E'$ over $t$ that factors through $E'.\mathrm{lev}$, the point $P$ followed by $q'$ factors through $E.\mathrm{lev}$.
--
--   This supplies the clause missing from the definition of an Atkin–Lehner quotient at a prime $r$ not dividing the level, namely that the dual isogeny also carries the level-$N$ structure of $E'$ into that of $E$, so that the pair $(q,q')$ is compatible with level structures in both directions. It is used in the rigidification step comparing the Atkin–Lehner involution with the relative Frobenius in the Čerednik–Drinfel'd uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_symm_of_isAtkinLehnerQuotientVia_of_not_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.preservesLevel_symm_of_isAtkinLehnerQuotientVia_of_not_dvd
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (r : ℕ) [Fact r.Prime] (hrN : ¬ r ∣ N)
    {S : Type} [CommRing S] (E E' : FakeEllipticCurve Λ N S)
    (q : E.A ⟶ E'.A) (hq : q ≫ E'.f = E.f) (q' : E'.A ⟶ E.A) (hq' : q' ≫ E.f = E'.f)
    (h : FakeEllipticCurve.IsAtkinLehnerQuotientVia r E E' q hq q' hq') :
    FakeEllipticCurve.PreservesLevel E' E q' hq' := by sorry
