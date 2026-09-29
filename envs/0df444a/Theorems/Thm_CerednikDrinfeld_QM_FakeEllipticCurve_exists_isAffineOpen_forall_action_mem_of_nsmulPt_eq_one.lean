-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAffineOpen_forall_action_mem_of_nsmulPt_eq_one
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isAffineOpen_forall_action_mem_of_nsmulPt_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/6efc8e80-4ea3-574f-9b90-1fc837460226
-- title:
--   Orbits of an n-torsion subscheme lie in affine opens
-- statement:
--   Let $a,b$ be rationals, $\Lambda$ a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, $N$ a natural number, $S$ a commutative ring, and let $E$ be a fake elliptic curve of type $(\Lambda,N)$ over $S$: in particular a scheme $E.A$ with a structure morphism $E.f : E.A \to \operatorname{Spec} S$ carrying a commutative relative group law $E.L$ (functorial multiplication, unit and inverse on sections $P : T \to E.A$ with $P \circ$ nothing — precisely, on pairs $\varphi : T \to E.A$ with $\varphi$ followed by $E.f$ equal to a given $t : T \to \operatorname{Spec} S$), together with the further data of the structure (quaternionic action, fibre dimension, and the remaining fields). Let $\iota : K \to E.A$ be a morphism of schemes, and $n$ a natural number with $n > 0$. Assume that every point of $E.A$ factoring through $\iota$ is killed by $n$: for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and every $P$ with $P$ followed by $E.f$ equal to $t$, if $P$ factors as $e$ followed by $\iota$ for some $e : T \to K$, then the $n$-fold $E.L$-sum of $P$ with itself is the unit section $E.L.one\ t$. Then for every point $x$ of the underlying space of $E.A$ there is an open $U \subseteq E.A$ that is an affine open such that, for every point $r$ of the underlying space of the fibre product of $\iota$ followed by $E.f$ with $E.f$, if the second projection sends $r$ to $x$ then $(E.L.action\ \iota)(r) \in U$, where $E.L.action\ \iota$ is the morphism $K \times_S E.A \to E.A$ given by the $E.L$-product of the two canonical points (first projection followed by $\iota$, and second projection) over the base $\operatorname{pullback.snd}$ followed by $E.f$.
--
--   This is the orbit-affineness hypothesis required to form a quotient of $E.A$ by the action of the finite flat subgroup scheme $K$ viewed as an action groupoid $K \times_S E.A \rightrightarrows E.A$; it is consumed by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_quotient_of_finiteFlat_stable_subgroup`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_quotient_of_finiteFlat_stable_subgroup). The base $S$ is an arbitrary commutative ring, so the statement is available in the relative setting in which the quotient fake elliptic curve is constructed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAffineOpen_forall_action_mem_of_nsmulPt_eq_one.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isAffineOpen_forall_action_mem_of_nsmulPt_eq_one
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) {K : Scheme.{u}} (ι : K ⟶ E.A)
    (n : ℕ) (hn : 0 < n)
    (hK : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      (∃ e : T ⟶ K, e ≫ ι = P.1) → nsmulPt E.L t n P = E.L.one t)
    (x : E.A) :
    ∃ U : E.A.Opens, IsAffineOpen U ∧
      ∀ r : ↑(pullback (ι ≫ E.f) E.f), (pullback.snd (ι ≫ E.f) E.f) r = x → (E.L.action ι) r ∈ U := by sorry
