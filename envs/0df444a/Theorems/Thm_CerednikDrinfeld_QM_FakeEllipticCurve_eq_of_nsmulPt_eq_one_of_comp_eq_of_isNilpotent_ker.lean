-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_of_nsmulPt_eq_one_of_comp_eq_of_isNilpotent_ker
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.eq_of_nsmulPt_eq_one_of_comp_eq_of_isNilpotent_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/d91ade16-bfbf-51de-baef-621a5b3a834c
-- title:
--   Unramifiedness of m-torsion: two m-torsion points agreeing on a thickening coincide
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a local commutative ring $S$. Let $E$ be a fake elliptic curve of type $(\Lambda,N)$ over $S$ in the sense of the project structure `FakeEllipticCurve`; of its components, the ones entering the statement are the scheme $E.A$ with structure morphism $E.f : E.A \to \operatorname{Spec} S$, the relative group law $E.L$ on $E.f$ (functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec} S$, with associativity, unit laws, inverses and compatibility with base change) and the commutativity of $E.L$; the remaining components (smoothness, properness and connectedness of fibres, fibres of dimension $2$, the action of $\Lambda$ with its trace condition, and the curve and level-$N$ data) are not referred to. Let $m$ be a natural number whose image in $S$ is a unit, let $i : T_0 \to T$ be a closed immersion of schemes whose ideal `i.ker` is nilpotent, and let $t : T \to \operatorname{Spec} S$ be a morphism. Let $P,P'$ be $T$-points of $E.A$ over $t$, i.e. morphisms $T \to E.A$ whose composite with $E.f$ is $t$, such that the $m$-fold sum of each under $E.L$ (defined recursively, the empty sum being the unit point) is the unit point over $t$, and such that $P$ and $P'$ become equal after composing with $i$. Then $P = P'$.
--
--   This is the pointwise, infinitesimal-criterion form of the assertion that multiplication by $m$ on a fake elliptic curve is formally unramified when $m$ is invertible on the base, so that $m$-torsion sections, and hence level-$m$ data, are determined by their restriction to any infinitesimal thickening. It supplies the uniqueness half of the statement that full level structures on fake elliptic curves deform uniquely, and is used in [`CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.existsUnique_comp_eq_specMap_comp_of_isNilpotent_ker`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.existsUnique_comp_eq_specMap_comp_of_isNilpotent_ker).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_of_nsmulPt_eq_one_of_comp_eq_of_isNilpotent_ker.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.eq_of_nsmulPt_eq_one_of_comp_eq_of_isNilpotent_ker
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S : Type u} [CommRing S] [IsLocalRing S] (E : FakeEllipticCurve Λ N S)
    (m : ℕ) (hm : IsUnit ((m : ℕ) : S))
    {T T₀ : Scheme.{u}} (i : T₀ ⟶ T) [IsClosedImmersion i] (hi : IsNilpotent i.ker)
    (t : T ⟶ Spec (CommRingCat.of S)) (P P' : SchemeHomOver t E.f)
    (hP : nsmulPt E.L t m P = E.L.one t) (hP' : nsmulPt E.L t m P' = E.L.one t)
    (h : i ≫ P.1 = i ≫ P'.1) :
    P = P' := by sorry
