-- Prove2me | Theorems.Thm_CombOpt_TotalUnimodularity_isTotallyUnimodular_iff_isUnimodular_fromCols_one
-- name    : CombOpt.TotalUnimodularity.isTotallyUnimodular_iff_isUnimodular_fromCols_one
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:05:02.726948+00:00
-- url     : https://prove2.me/theorems/5f68c39f-f901-45ac-8852-bf40ebcc52e6
-- title:
--   §6.5 (Exercise 6.23) — $A$ is totally unimodular iff $[A\ I]$ is unimodular
-- statement:
--   Let $A$ be an integral $m\times n$ matrix and $I$ the $m\times m$ identity matrix. Then
--   $$A\ \text{is totally unimodular}\quad\Longleftrightarrow\quad [A\ I]\ \text{is unimodular}.$$
--   Here $A$ is **totally unimodular** if every square submatrix of $A$ has determinant $0$, $1$ or $-1$, and $[A\ I]$, which always has full row rank, is **unimodular** if every basis (nonsingular $m\times m$ column submatrix) has determinant $\pm1$.
--
--   This identity is the link between the inequality form $Ax\le b,\ x\ge0$ and the equality form $[A\ I]z=b,\ z\ge0$, through which the Hoffman–Kruskal theorem follows from the Veinott–Dantzig theorem.
--
--   **Formalization Note** Total unimodularity is Mathlib's `Matrix.IsTotallyUnimodular` (square submatrices selected by injective row and column maps; a reordering only changes the sign of the determinant). $[A\ I]$ is `Matrix.fromCols A 1`, with columns indexed by `Fin n ⊕ Fin m`.
--
--   Differences from the source:
--   - encoding: an $m\times n$ matrix $A$ (integral, as Exercise 6.23 states) → `Matrix (Fin m) (Fin n) ℤ`; reason: both sides force integer entries (a totally unimodular matrix has entries in $\{0,\pm1\}$, a unimodular matrix is integral by definition), so integer matrices lose no instance where either side holds
--   - encoding: all square submatrices of $A$ → Mathlib `Matrix.IsTotallyUnimodular`, square submatrices selected by injective row and column maps, so also with rows and columns reordered; reason: a reordering changes only the sign of the determinant and $\{0,\pm1\}$ is closed under sign; same instances
--   - encoding: a basis of $A$, a set of $m$ columns, and "unimodular" defined only under full row rank → `IsUnimodular`: an injective `f : Fin m → ι` listing the columns in some order, with full row rank a clause of the predicate; reason: a reordering changes only the sign of the determinant, and the rank clause always holds for $[A\ I]$; same instances
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.5, p. 221 (PDF p. 229); Exercise 6.23, p. 224 (PDF p. 232)

import Mathlib
import Definitions.Def_CombOpt_TotalUnimodularity_IsUnimodular

namespace CombOpt.TotalUnimodularity

open Matrix

/-- **§6.5 (Exercise 6.23): `A` is totally unimodular iff `[A I]` is unimodular.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.5,
p. 221 (PDF p. 229): "Moreover, it is easy to see that an m by n matrix A is totally unimodular
if and only if [A I] is unimodular, where I is the m by m identity matrix. (Exercise 6.23.)";
Exercise 6.23, p. 224 (PDF p. 232): "Let A be an integral m by n matrix. Show that A is totally
unimodular if and only if [A I] is unimodular, where I is the m by m identity matrix."

For an integer `m × n` matrix `A`, `A` is totally unimodular (every square submatrix has
determinant `0`, `1` or `−1`) if and only if the `m × (n + m)` matrix `[A I]` is unimodular
(`IsUnimodular`: it has full row rank, which `[A I]` always has, and every basis has determinant
`±1`).

**Formalization Note.** Total unimodularity is Mathlib's `Matrix.IsTotallyUnimodular` (square
submatrices chosen by injective row and column maps, i.e. the book's square submatrices up to a
reordering, which changes only the sign of the determinant). `[A I]` is
`Matrix.fromCols A 1`, with columns indexed by `Fin n ⊕ Fin m`. -/
theorem isTotallyUnimodular_iff_isUnimodular_fromCols_one {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) :
    A.IsTotallyUnimodular ↔
      IsUnimodular (Matrix.fromCols A (1 : Matrix (Fin m) (Fin m) ℤ)) := by sorry

end CombOpt.TotalUnimodularity
