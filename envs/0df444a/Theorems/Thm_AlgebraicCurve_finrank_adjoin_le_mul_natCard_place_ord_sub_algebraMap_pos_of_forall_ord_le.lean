-- Prove2me | Theorems.Thm_AlgebraicCurve_finrank_adjoin_le_mul_natCard_place_ord_sub_algebraMap_pos_of_forall_ord_le
-- name    : AlgebraicCurve.finrank_adjoin_le_mul_natCard_place_ord_sub_algebraMap_pos_of_forall_ord_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/d9c2c4cb-369e-5d8d-b628-33ec3d8e2a1b
-- title:
--   Degree bound from a fibre with bounded multiplicities
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field extension of $K$ (an extension in the sense of a $K$-algebra structure on the field $F$). Let $x \in F$ be transcendental over $K$, and assume $F$ is finite-dimensional over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`. Here a place of $F$ over $K$ is, by definition, a valuation subring of $F$ that contains $\operatorname{algebraMap} K F(a)$ for every $a \in K$, is not all of $F$, and is a principal ideal ring; for such a place $v$ and $f \in F$, $v.\mathrm{ord}(f)$ is the integer $-\log$ of the value of $f$ under the $\mathbb{Z}^{m0}$-valued adic valuation attached to the height-one prime of that subring. Let $a \in K$ and let $e$ be a natural number such that for every place $v$ with $v.\mathrm{ord}(x - \operatorname{algebraMap} K F(a)) > 0$ one has $v.\mathrm{ord}(x - \operatorname{algebraMap} K F(a)) \le e$. The conclusion is the inequality of natural numbers $$[F : K(x)] \le e \cdot \#\{v : v.\mathrm{ord}(x - \operatorname{algebraMap} K F(a)) > 0\},$$ the cardinality being `Nat.card` of the subtype of places at which $x - a$ has positive order.
--
--   This is the elementary half of the fundamental identity for the function $x-a$ on a curve over an algebraically closed field: the degree of the zero divisor of $x-a$ equals $[F:K(x)]$, so an upper bound $e$ on the multiplicities forces the fibre above $a$ to have at least $[F:K(x)]/e$ points. It is used to bound from below the number of points in a fibre of a map of modular curves, in [`ModularCurve.sub_one_mul_index_gamma1_le_twelve_mul_natCard_evalAt_mem_ssJSet_x1FunctionFieldC`](thm.html#ModularCurve.sub_one_mul_index_gamma1_le_twelve_mul_natCard_evalAt_mem_ssJSet_x1FunctionFieldC).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finrank_adjoin_le_mul_natCard_place_ord_sub_algebraMap_pos_of_forall_ord_le.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.finrank_adjoin_le_mul_natCard_place_ord_sub_algebraMap_pos_of_forall_ord_le
    (K : Type*) [Field K] [IsAlgClosed K] {F : Type*} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F) (a : K) (e : ℕ)
    (he : ∀ v : AlgebraicCurve.Place K F, 0 < v.ord (x - algebraMap K F a) → v.ord (x - algebraMap K F a) ≤ e) :
    Module.finrank ↥(IntermediateField.adjoin K ({x} : Set F)) F ≤
      e * Nat.card {v : AlgebraicCurve.Place K F // 0 < v.ord (x - algebraMap K F a)} := by sorry
