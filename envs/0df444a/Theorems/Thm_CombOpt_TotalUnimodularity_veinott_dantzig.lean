-- Prove2me | Theorems.Thm_CombOpt_TotalUnimodularity_veinott_dantzig
-- name    : CombOpt.TotalUnimodularity.veinott_dantzig
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:05:52.632312+00:00
-- url     : https://prove2.me/theorems/9b912a75-48b8-49ad-84cd-12db501076af
-- title:
--   Theorem 6.24 (Veinott–Dantzig) — $\{x : Ax=b,\ x\ge0\}$ is integral for all integral $b$ iff $A$ is unimodular
-- statement:
--   Let $A$ be an integral $m\times n$ matrix of full row rank. Then the polyhedron
--   $$\{x\in\mathbb R^n : Ax=b,\ x\ge 0\}$$
--   is integral (every nonempty face contains an integral vector) for every integral vector $b\in\mathbb R^m$ if and only if $A$ is unimodular (every basis of $A$ has determinant $\pm1$).
--
--   This is the equality-form integrality theorem from which the Hoffman–Kruskal theorem follows by adding slack variables.
--
--   **Formalization Note** $A$ has integer entries and acts on $\mathbb R^n$ through its real cast; full row rank is the rank of that cast. Integral $b$ is the cast of $b\in\mathbb Z^m$, and every such $b$ is quantified, including those for which the polyhedron is empty. Integrality is `IsIntegralPolyhedron` (faces, as in the book) and unimodularity is `IsUnimodular`.
--
--   Differences from the source:
--   - encoding: integral matrix $A$ and integral $b\in\mathbb R^m$ → `Matrix (Fin m) (Fin n) ℤ` acting through its real cast, $b$ the cast of `Fin m → ℤ`; reason: Lean convention for integral data; same instances
--   - encoding: a basis of $A$, a set of $m$ columns, and "unimodular" defined only under full row rank → `IsUnimodular`: an injective `f : Fin m → ι` listing the columns in some order, with full row rank a clause of the predicate; reason: a reordering changes only the sign of the determinant, and the rank clause is the hypothesis `hA`; same instances
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 6.24, p. 220 (PDF p. 228)

import Mathlib
import Definitions.Def_CombOpt_TotalUnimodularity_IsIntegralPolyhedron
import Definitions.Def_CombOpt_TotalUnimodularity_IsUnimodular

namespace CombOpt.TotalUnimodularity

open Matrix

/-- **Theorem 6.24 (Veinott–Dantzig).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998),
Theorem 6.24, p. 220 (PDF p. 228): "Let A be an integral m by n matrix of full row rank. Then
the polyhedron defined by Ax = b, x ≥ 0 is integral for every integral vector b ∈ Rᵐ if and only
if A is unimodular."

For an integer `m × n` matrix `A` whose real cast has rank `m`, the polyhedron
`{x ∈ ℝⁿ : A x = b, x ≥ 0}` is integral (`IsIntegralPolyhedron`: every nonempty face contains an
integral vector) for every `b ∈ ℤᵐ` if and only if `A` is unimodular (`IsUnimodular`: every basis
has determinant `±1`).

**Formalization Note.** `A` has entries in `ℤ` and acts on `ℝⁿ` through its real cast; an
integral `b ∈ ℝᵐ` is the cast of `b : Fin m → ℤ`; `x ≥ 0` is the pointwise order. Full row rank
is the rank of the real cast. The book's definition of unimodular presupposes full row rank,
and `IsUnimodular` includes it, so under `hA` it is exactly the basis condition. -/
theorem veinott_dantzig {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : (A.map (Int.cast : ℤ → ℝ)).rank = m) :
    (∀ b : Fin m → ℤ, IsIntegralPolyhedron
        {x : Fin n → ℝ | A.map (Int.cast : ℤ → ℝ) *ᵥ x = (fun i => (b i : ℝ)) ∧ 0 ≤ x}) ↔
      IsUnimodular A := by sorry

end CombOpt.TotalUnimodularity
