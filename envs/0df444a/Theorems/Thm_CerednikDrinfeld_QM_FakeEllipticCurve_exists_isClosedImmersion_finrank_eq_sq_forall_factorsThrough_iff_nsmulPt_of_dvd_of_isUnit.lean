-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isClosedImmersion_finrank_eq_sq_forall_factorsThrough_iff_nsmulPt_of_dvd_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isClosedImmersion_finrank_eq_sq_forall_factorsThrough_iff_nsmulPt_of_dvd_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/a508bf96-86b3-5418-a710-9fa8531d31c7
-- title:
--   n-torsion in the level structure: finite flat of rank n²
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $M$ and a commutative ring $S$ in which the image of $M$ is a unit, and let $E$ be a fake elliptic curve of level $M$ over $S$ for $\Lambda$: this packages a scheme $E.A$ with a structure morphism $E.f : E.A \to \operatorname{Spec} S$, a relative group law $E.L$ on $T$-valued points over $\operatorname{Spec} S$ which is commutative, the bundle of abelian-scheme properties for $E.f$ (smooth, proper, connected fibres, admitting a relative group law), fibres of topological Krull dimension $2$, an additive action of $\Lambda$ by $S$-endomorphisms compatible with the group law and satisfying the trace condition on tangent spaces, together with a level structure given by a morphism $E.\mathrm{lev}$ from a scheme $E.C$ into $E.A$. Let $n$ divide $M$. The assertion is the existence of a scheme $C_n$ and a morphism $\mathrm{lev}_n : C_n \to E.A$ such that: $\mathrm{lev}_n$ is a closed immersion; the composite $E.f \circ \mathrm{lev}_n$ is finite, flat and locally of finite presentation; its fibre rank at every point of $\operatorname{Spec} S$ equals $n^2$; and for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and every $T$-point $P$ of $E.A$ over $t$ (a morphism $T \to E.A$ whose composite with $E.f$ is $t$), $P$ factors through $\mathrm{lev}_n$ (i.e. $P = \mathrm{lev}_n \circ P_0$ for some $P_0 : T \to C_n$) if and only if $P$ factors through $E.\mathrm{lev}$ and the $n$-fold sum of $P$ for the group law $E.L$ over $t$ is the unit section over $t$.
--
--   This constructs the $n$-torsion subscheme $C[n] = C \times_A A[n]$ of the level-$M$ structure on a fake elliptic curve, for $n \mid M$ with $M$ invertible on the base, as a finite flat closed subscheme of rank $n^2$ characterised by its functor of points. It feeds the construction of extra level structure for fake elliptic curves, where a level-$M$ structure is refined along a factorisation of $M$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isClosedImmersion_finrank_eq_sq_forall_factorsThrough_iff_nsmulPt_of_dvd_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isClosedImmersion_finrank_eq_sq_forall_factorsThrough_iff_nsmulPt_of_dvd_of_isUnit
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {M : ℕ}
    (S : Type) [CommRing S] (hM : IsUnit ((M : ℕ) : S)) (E : FakeEllipticCurve Λ M S) (n : ℕ) (hn : n ∣ M) :
    ∃ (Cn : Scheme.{0}) (levn : Cn ⟶ E.A), IsClosedImmersion levn ∧
      IsFinite (levn ≫ E.f) ∧ Flat (levn ≫ E.f) ∧ LocallyOfFinitePresentation (levn ≫ E.f) ∧
      (∀ s : ↥(Spec (CommRingCat.of S)), (levn ≫ E.f).finrank s = n ^ 2) ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
        FactorsThrough levn P ↔ FactorsThrough E.lev P ∧ nsmulPt E.L t n P = E.L.one t := by sorry
