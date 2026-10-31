-- Prove2me | Theorems.Thm_CombOpt_TotalUnimodularity_hoffman_kruskal
-- name    : CombOpt.TotalUnimodularity.hoffman_kruskal
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:05:59.706409+00:00
-- url     : https://prove2.me/theorems/d9e81783-2edc-42ef-ab97-e62f83238214
-- title:
--   Theorem 6.25 (Hoffman–Kruskal) — $\{x : Ax\le b,\ x\ge0\}$ is integral for every integral $b$ iff $A$ is totally unimodular
-- statement:
--   Let $A$ be an integral $m\times n$ matrix. Then the polyhedron
--   $$\{x\in\mathbb R^n : Ax\le b,\ x\ge 0\}$$
--   is integral (every nonempty face contains an integral vector) for every integral vector $b\in\mathbb R^m$ if and only if $A$ is **totally unimodular**, i.e. every square submatrix of $A$ has determinant $0$, $1$ or $-1$.
--
--   This characterization is the main reason total unimodularity is central to combinatorial optimization: for a totally unimodular constraint matrix, every integer program $\max\{c^\top x : Ax\le b,\ x\ge 0,\ x\in\mathbb Z^n\}$ with integral $b$ is solved by its linear programming relaxation, and conversely total unimodularity is the only property of $A$ that guarantees this for all integral right-hand sides.
--
--   **Formalization Note** $A$ has integer entries and acts on $\mathbb R^n$ through its real cast; integral $b$ is the cast of $b\in\mathbb Z^m$, and every such $b$ is quantified, including those for which the polyhedron is empty. Integrality is `IsIntegralPolyhedron` (faces, as in the book); total unimodularity is Mathlib's `Matrix.IsTotallyUnimodular`.
--
--   Differences from the source:
--   - encoding: integral matrix $A$ and integral $b\in\mathbb R^m$ → `Matrix (Fin m) (Fin n) ℤ` acting through its real cast, $b$ the cast of `Fin m → ℤ`; reason: Lean convention for integral data; same instances
--   - encoding: all square submatrices of $A$ → Mathlib `Matrix.IsTotallyUnimodular`, square submatrices selected by injective row and column maps, so also with rows and columns reordered; reason: a reordering changes only the sign of the determinant and $\{0,\pm1\}$ is closed under sign; same instances
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 6.25, p. 221 (PDF p. 229)

import Mathlib
import Definitions.Def_CombOpt_TotalUnimodularity_IsIntegralPolyhedron

namespace CombOpt.TotalUnimodularity

open Matrix

/-- **Theorem 6.25 (Hoffman–Kruskal Theorem).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998),
Theorem 6.25, p. 221 (PDF p. 229): "Let A be an m by n integral matrix. Then the polyhedron
defined by Ax ≤ b, x ≥ 0 is integral for every integral vector b ∈ Rᵐ if and only if A is
totally unimodular."

For an integer `m × n` matrix `A`, the polyhedron `{x ∈ ℝⁿ : A x ≤ b, x ≥ 0}` is integral
(`IsIntegralPolyhedron`: every nonempty face contains an integral vector) for every `b ∈ ℤᵐ`
if and only if `A` is totally unimodular.

**Formalization Note.** `A` has entries in `ℤ` and acts on `ℝⁿ` through its real cast; an
integral `b ∈ ℝᵐ` is the cast of `b : Fin m → ℤ`; `≤` on vectors is pointwise. Every integral
`b` is quantified, including those for which the polyhedron is empty (the empty polyhedron is
integral). Total unimodularity is Mathlib's `Matrix.IsTotallyUnimodular` of the integer matrix
(every square submatrix has determinant `0`, `1` or `−1`; integer and real determinants agree). -/
theorem hoffman_kruskal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (∀ b : Fin m → ℤ, IsIntegralPolyhedron
        {x : Fin n → ℝ | A.map (Int.cast : ℤ → ℝ) *ᵥ x ≤ (fun i => (b i : ℝ)) ∧ 0 ≤ x}) ↔
      A.IsTotallyUnimodular := by sorry

end CombOpt.TotalUnimodularity
