-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_divisor_eq_floor_and_mul_degree_le_of_min_ord_le
-- name    : AlgebraicCurve.exists_divisor_eq_floor_and_mul_degree_le_of_min_ord_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/e0793820-aeea-5c32-9272-1d20e99c73d6
-- title:
--   Floor divisor of m(div f-min(0,div x))/d and its degree
-- statement:
--   Let $k$ be an algebraically closed field and $F$ a field equipped with a $k$-algebra structure, let $x \in F$ be transcendental over $k$, and assume $F$ is finite-dimensional over the intermediate field $k(x) =$ `IntermediateField.adjoin k {x}`. Let $f \in F$ be nonzero and suppose that for every place $v$ of $F$ over $k$ — that is, every valuation subring of $F$ containing $k$, distinct from $F$ itself and a principal ideal ring — one has $\min(0, \operatorname{ord}_v x) \le \operatorname{ord}_v f$, where $\operatorname{ord}_v$ denotes the integer-valued order function attached to $v$ (minus the logarithm of the associated adic valuation). Let $m, d$ be natural numbers with $d > 0$. Then there exists a divisor $E$, i.e. a finitely supported function from the places of $F$ over $k$ to $\mathbb{Z}$, such that for every place $v$ the value $E(v)$ equals the integer quotient $\bigl(m\,(\operatorname{ord}_v f - \min(0,\operatorname{ord}_v x))\bigr)/d$, which since $d>0$ is the floor of that rational number, and such that $d \cdot \deg E \le m \cdot [F : k(x)]$, where $\deg E = \sum_v E(v)\cdot \deg v$ is the degree homomorphism on divisors.
--
--   This is the elementary divisor bookkeeping that produces, for a function $f$ whose poles are bounded by those of $x$, the floor divisor $\lfloor m(\operatorname{div} f - \min(0,\operatorname{div} x))/d\rfloor$ together with the bound $d \deg E \le m[F:k(x)]$. It is used in the order computations on the function field of $X_1(M)$, with $d = 12$ and $m$ a weight, where the reference divisor of a power of the Hodge bundle is analysed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_divisor_eq_floor_and_mul_degree_le_of_min_ord_le.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open scoped IntermediateField

theorem AlgebraicCurve.exists_divisor_eq_floor_and_mul_degree_le_of_min_ord_le
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (f : F) (hf : f ≠ 0) (hfx : ∀ v : Place k F, min 0 (v.ord x) ≤ v.ord f)
    (m d : ℕ) (hd : 0 < d) :
    ∃ E : Divisor k F,
      (∀ v : Place k F, E v = ((m : ℤ) * (v.ord f - min 0 (v.ord x))) / (d : ℤ)) ∧
      (d : ℤ) * E.degree ≤ (m : ℤ) * (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by sorry
