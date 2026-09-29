-- Prove2me | Theorems.Thm_AlgebraicCurve_discr_ne_zero_of_normalForm_split
-- name    : AlgebraicCurve.discr_ne_zero_of_normalForm_split
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/fb772794-198b-5e7f-a3ab-62ce0523d595
-- title:
--   Nonzero discriminant for split normal-form algebras over K[X]
-- statement:
--   Let $K$ be a field, $n$ a natural number, and $B$ a commutative ring equipped with a $K[X]$-algebra structure admitting a $K[X]$-basis $b_0,\dots,b_n$ indexed by $\mathrm{Fin}(n+1)$, together with weights $d_i \in \mathbb{N}$. Assume $b_0 = 1$ and $d_0 = 0$, that $d_i \in \{1,2\}$ for every $i \neq 0$, and that the structure constants satisfy the degree bound: for all indices $i,j,k$ with $i \neq 0$ and $j \neq 0$, the $b_k$-coordinate of $b_i b_j$ with respect to $b$ has degree at most $d_i + d_j - d_k$ (truncated subtraction in $\mathbb{N}$). Assume further that the leading behaviour at infinity splits, in the sense that there is a family $\tau_{j i} \in K$ ($j,i \in \mathrm{Fin}(n+1)$) whose determinant, as a matrix, is a unit, with $\tau_{j 0} = 1$ for all $j$, and such that for all $j$ and all $i,i' \neq 0$ one has $\tau_{j i}\tau_{j i'} = \sum_k c_{i i' k}\,\tau_{j k}$, where $c_{i i' k}$ is the coefficient of $X^{d_i + d_{i'} - d_k}$ in the $b_k$-coordinate of $b_i b_{i'}$. Then the discriminant $\mathrm{Algebra.discr}\ K[X]\ b$, that is $\det\big(\mathrm{Tr}_{B/K[X]}(b_i b_j)\big)_{i,j}$, is nonzero in $K[X]$.
--
--   This is the generic-étaleness criterion for a normal-form presentation of a curve over the affine line: when the algebra of leading forms at infinity is split (diagonalised by the matrix $\tau$), the trace form of the given basis is nondegenerate over $K[X]$, so the total ring of fractions of $B$ is étale over $K(X)$. It is used in the construction of lifts of normal-form structure constants, via [`AlgebraicCurve.exists_lift_normalForm_structureConstants_of_smallExtension`](thm.html#AlgebraicCurve.exists_lift_normalForm_structureConstants_of_smallExtension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_discr_ne_zero_of_normalForm_split.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

universe u v

theorem AlgebraicCurve.discr_ne_zero_of_normalForm_split
    (K : Type u) [Field K] (n : ℕ) (B : Type v) [CommRing B] [Algebra K[X] B]
    (b : Module.Basis (Fin (n + 1)) K[X] B) (d : Fin (n + 1) → ℕ)
    (hb0 : b 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k)
    (hinf : ∃ τ : Fin (n + 1) → Fin (n + 1) → K,
      IsUnit (Matrix.det (Matrix.of τ)) ∧
      (∀ j, τ j 0 = 1) ∧
      ∀ j i i', i ≠ 0 → i' ≠ 0 →
        τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k) :
    Algebra.discr K[X] b ≠ 0 := by sorry
