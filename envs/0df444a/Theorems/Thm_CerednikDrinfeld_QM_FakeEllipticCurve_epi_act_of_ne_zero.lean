-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_epi_act_of_ne_zero
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.epi_act_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/513293b3-e696-501f-a369-126fa6d08cd5
-- title:
--   Integer multiplication on a fake elliptic curve is epi
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the rational quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and assume that $\Lambda$ contains the image of every integer $m$ under $\mathbb{Z}\to\mathbb{Q}\to\mathbb{H}[\mathbb{Q},a,b]$. Let $N$ be a natural number, let $k$ be a field (in the ground universe), and let $E$ be a `FakeEllipticCurve` for $\Lambda$ and level $N$ over $k$: among its data it carries a scheme $A$ with a structure morphism $f : A \to \operatorname{Spec} k$, a relative group law $L$ on $f$ (functorial multiplication, unit and inverse on $T$-points over the base, with the group axioms and compatibility with base change) which is commutative, the property bundle asserting that $f$ is smooth and proper with connected fibres and admits a group law, the requirement that every fibre of $f$ have topological Krull dimension $2$, and an action `act` assigning to each $x \in \Lambda$ an endomorphism of $A$ over $\operatorname{Spec} k$, additive in $x$ on $T$-points, anti-multiplicative in the sense that `act` of $xy$ is `act` of $y$ followed by `act` of $x$, sending $1$ to the identity, and satisfying a trace condition on tangent vectors at geometric points. Let $m$ be a nonzero integer. The assertion is that the endomorphism of $A$ given by the action of the element of $\Lambda$ determined by $m$ is an epimorphism in the category of schemes.
--
--   This is the statement that multiplication by a nonzero integer on the abelian surface underlying a fake elliptic curve, realised here through the quaternionic action of the integer scalars, is an epimorphism of schemes. It is used in the construction of level structures and Atkin–Lehner quotients for fake elliptic curves, where epimorphy allows morphisms out of $A$ to be cancelled on the right.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_epi_act_of_ne_zero.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.epi_act_of_ne_zero
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {N : ℕ}
    (k : Type) [Field k] (E : FakeEllipticCurve Λ N k) (m : ℤ) (hm : m ≠ 0) :
    Epi (E.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩) := by sorry
