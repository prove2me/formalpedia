-- Prove2me | Theorems.Thm_CombOpt_TotalUnimodularity_isIntegralPolyhedron_of_isTotallyUnimodular
-- name    : CombOpt.TotalUnimodularity.isIntegralPolyhedron_of_isTotallyUnimodular
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:06:00.415756+00:00
-- url     : https://prove2.me/theorems/2bb72bc0-1090-4429-8ed8-92305deb9e68
-- title:
--   Theorem 6.26 — for totally unimodular $A$ and integral $b$, $\{x : Ax\le b\}$ is integral
-- statement:
--   Let $A$ be an $m\times n$ totally unimodular matrix (every square submatrix has determinant $0$, $1$ or $-1$) and let $b\in\mathbb R^m$ be an integral vector. Then the polyhedron
--   $$\{x\in\mathbb R^n : Ax\le b\}$$
--   is integral: every nonempty face contains an integral vector.
--
--   Unlike the Hoffman–Kruskal theorem, no nonnegativity constraints are needed, and the polyhedron need not have vertices. This is the form used to deduce integrality of bipartite matching, flow and interval-matrix polyhedra.
--
--   **Formalization Note** $A$ is a real matrix, as in the book; total unimodularity forces its entries into $\{0,\pm1\}$, so the polyhedron is rational and no separate integrality assumption on $A$ is made. Integral $b$ is the cast of $b\in\mathbb Z^m$.
--
--   Differences from the source:
--   - encoding: integral vector $b\in\mathbb R^m$ → the real cast of `b : Fin m → ℤ`; reason: Lean convention for integral data; same instances
--   - encoding: all square submatrices of $A$ → Mathlib `Matrix.IsTotallyUnimodular`, square submatrices selected by injective row and column maps, so also with rows and columns reordered; reason: a reordering changes only the sign of the determinant and $\{0,\pm1\}$ is closed under sign; same instances
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 6.26, p. 221 (PDF p. 229)

import Mathlib
import Definitions.Def_CombOpt_TotalUnimodularity_IsIntegralPolyhedron

namespace CombOpt.TotalUnimodularity

open Matrix

/-- **Theorem 6.26 (TU matrices give integral polyhedra without nonnegativity).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998),
Theorem 6.26, p. 221 (PDF p. 229): "Let A be an m by n totally unimodular matrix and let
b ∈ Rᵐ be an integral vector. Then the polyhedron defined by Ax ≤ b is integral."

For a real `m × n` totally unimodular matrix `A` and `b ∈ ℤᵐ`, the polyhedron
`{x ∈ ℝⁿ : A x ≤ b}` is integral (`IsIntegralPolyhedron`: every nonempty face contains an
integral vector).

**Formalization Note.** `A` is real, as in the book; total unimodularity (Mathlib's
`Matrix.IsTotallyUnimodular`) forces every entry into `{0, 1, −1}`, so the polyhedron is
rational. No integrality of `A` is assumed separately. -/
theorem isIntegralPolyhedron_of_isTotallyUnimodular {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.IsTotallyUnimodular) (b : Fin m → ℤ) :
    IsIntegralPolyhedron {x : Fin n → ℝ | A *ᵥ x ≤ (fun i => (b i : ℝ))} := by sorry

end CombOpt.TotalUnimodularity
