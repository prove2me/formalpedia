-- Prove2me | Theorems.Thm_AlgebraicCurve_linearIndependent_pow_mul
-- name    : AlgebraicCurve.linearIndependent_pow_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/cb876ba6-ecd7-54ac-9853-98e43065b07c
-- title:
--   Linear independence of the products x^j uᵢ
-- statement:
--   Let $K$, $E$, $F$ be fields forming a tower: $E$ and $F$ are $K$-algebras, $F$ is an $E$-algebra, and the three structures are compatible as a scalar tower over $K$. Let $x \in E$, let $n$ be a natural number, and let $u : \mathrm{Fin}\,n \to F$ be a finite family of elements of $F$. Assume that the family of powers $(x^j)_{j \in \mathbb{N}}$ is linearly independent over $K$ (that is, $x$ is transcendental over $K$), and that the family $u$ is linearly independent over $E$. The conclusion is that the family indexed by $\mathbb{N} \times \mathrm{Fin}\,n$ which sends a pair $(j, i)$ to $\xi^j \, u_i$, where $\xi$ denotes the image of $x$ in $F$ under the structure map $E \to F$, is linearly independent over $K$. Note that the index set of the conclusion is infinite, the exponent $j$ ranging over all of $\mathbb{N}$, while the second index ranges over the finite set $\mathrm{Fin}\,n$; linear independence is therefore the assertion that every finitely supported $K$-linear relation among the $\xi^j u_i$ has all coefficients zero.
--
--   This is the standard linear-independence step in the theory of algebraic function fields: a transcendental element of an intermediate field together with an $E$-free family in the upper field produces a $K$-free family of products. It supplies the linear-independence clause used in assembling pole-divisor data, and is cited in the proof of [`AlgebraicCurve.Divisor.finrank_adjoin_le_degree_of_eq_max_neg_ord`](thm.html#AlgebraicCurve.Divisor.finrank_adjoin_le_degree_of_eq_max_neg_ord).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_linearIndependent_pow_mul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PoleDivisorPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem linearIndependent_pow_mul {K : Type*} {E : Type*} {F : Type*} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F] {x : E} {n : ℕ} {u : Fin n → F}
    (hx : LinearIndependent K (fun j : ℕ => x ^ j)) (hu : LinearIndependent E u) :
    LinearIndependent K (fun p : ℕ × Fin n => (algebraMap E F x) ^ p.1 * u p.2) := by sorry
