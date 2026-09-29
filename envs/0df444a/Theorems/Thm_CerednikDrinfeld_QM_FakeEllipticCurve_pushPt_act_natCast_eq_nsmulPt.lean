-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/bb39fa25-b416-56d7-b2a0-5948ada74b2c
-- title:
--   Action of n∈Λ is n-fold addition on points
-- statement:
--   Let $a,b$ be rationals, let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, let $N$ be a natural number, let $S$ be a commutative ring, and let $E$ be a fake elliptic curve of type `FakeEllipticCurve Λ N S`: in particular $E$ carries a scheme `E.A` with a structural morphism `E.f : E.A ⟶ Spec (CommRingCat.of S)`, a relative group law `E.L` on the functor of points of `E.f` (a functorial multiplication, unit and inverse satisfying the group axioms), and an action `E.act` assigning to each $x\in\Lambda$ an endomorphism of `E.A` over $\mathrm{Spec}\,S$, subject to the clauses `act_one`, `act_mul`, `act_add`, `act_hom` and `act_trace`. Assume $1\in\Lambda$, let $n$ be a natural number whose image $(n:\mathbb{Q})$ in $\mathbb{H}[\mathbb{Q},a,b]$ lies in $\Lambda$, let $T$ be a scheme with a morphism $t : T \to \mathrm{Spec}\,S$, and let $P$ be a $T$-point of `E.f` over $t$, that is a morphism $P : T \to E.A$ with $P$ followed by `E.f` equal to $t$. Then the point obtained by composing $P$ with the endomorphism `E.act ⟨(n : ℚ), hn⟩` coincides with `nsmulPt E.L t n P`, the $n$-fold sum of $P$ with itself for the group law `E.L`, defined recursively by the unit point at $n=0$ and by `E.L.mul t (nsmulPt E.L t m P) P` at $m+1$.
--
--   This identifies the two ways of speaking about multiplication by a natural number on a fake elliptic curve: the quaternionic action of the scalar $n\in\Lambda$, in which conditions such as $\varphi\psi = [n]$ are phrased at the level of morphisms, and the iterate of the relative group law on points, in which torsion conditions and Frobenius–Verschiebung relations are phrased. It is used throughout the level-structure and isogeny-factorisation arguments for fake elliptic curves, for instance in the transfer and factorisation statements for extra level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩) (E.act_over _) P = nsmulPt E.L t n P := by sorry
