-- Prove2me | Theorems.Thm_CombOpt_TotalUnimodularity_minimal_face_eq_affine
-- name    : CombOpt.TotalUnimodularity.minimal_face_eq_affine
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:05:51.890973+00:00
-- url     : https://prove2.me/theorems/08931554-3b0e-407d-acb4-0ccf1afbff82
-- title:
--   Proposition 6.7 — a minimal nonempty face of $\{x : Ax\le b\}$ is $\{x : A^\circ x=b^\circ\}$ with $\operatorname{rank}A^\circ=\operatorname{rank}A$
-- statement:
--   Let $A$ be a real $m\times n$ matrix, $b\in\mathbb R^m$, and $P=\{x\in\mathbb R^n : Ax\le b\}$. Let $F$ be a minimal nonempty face of $P$. Then there is a subsystem $A^\circ x\le b^\circ$ of $Ax\le b$ (a subset of its rows) such that
--   $$F=\{x\in\mathbb R^n : A^\circ x=b^\circ\}\qquad\text{and}\qquad \operatorname{rank}A^\circ=\operatorname{rank}A.$$
--
--   So minimal nonempty faces are affine subspaces, cut out by equality in some of the defining inequalities. In particular, $P$ has a vertex if and only if $A$ has full column rank, and in the proof of Theorem 6.26 it reduces integrality of $\{x : Ax\le b\}$ to solving a square nonsingular system.
--
--   **Formalization Note** The subsystem is given by a finite set $S$ of row indices (possibly empty); $A^\circ$ is the submatrix of the rows in $S$. The set $\{x : A^\circ x = b^\circ\}$ is the whole affine subspace, not intersected with $P$, exactly as stated. Ranks are ranks of real matrices.
--
--   Differences from the source:
--   - encoding: a subsystem $A^\circ x\le b^\circ$ of $Ax\le b$ → a `Finset` $S$ of row indices with $A^\circ$ = `A.submatrix (↑) id`; reason: a subsystem is a choice of rows; same instances
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Proposition 6.7, p. 205 (PDF p. 213)

import Mathlib
import Definitions.Def_CombOpt_TotalUnimodularity_IsMinimalNonemptyFace

namespace CombOpt.TotalUnimodularity

open Matrix

/-- **Proposition 6.7 (minimal faces are affine subspaces).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998),
Proposition 6.7, p. 205 (PDF p. 213): "Let F be a minimal nonempty face of P = {x : Ax ≤ b}.
Then F = {x : A°x = b°} for some subsystem A°x ≤ b° of Ax ≤ b. Moreover, the rank of the
matrix A° is equal to the rank of A."

For a real `m × n` matrix `A`, a vector `b ∈ ℝᵐ` and a minimal nonempty face `F` of
`P = {x : A x ≤ b}`, there is a set `S` of row indices such that `F` is the whole affine set
`{x ∈ ℝⁿ : (A x)ᵢ = bᵢ for all i ∈ S}` (not intersected with `P`), and the submatrix of `A`
formed by the rows in `S` has the same rank as `A`.

**Formalization Note.** A subsystem `A°x ≤ b°` is given by its set `S` of row indices (possibly
empty); `A°` is `A.submatrix (↑) id` with rows indexed by `S`. Ranks are ranks of real
matrices. -/
theorem minimal_face_eq_affine {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (F : Set (Fin n → ℝ))
    (hF : IsMinimalNonemptyFace {x : Fin n → ℝ | A *ᵥ x ≤ b} F) :
    ∃ S : Finset (Fin m),
      F = {x : Fin n → ℝ | ∀ i ∈ S, (A *ᵥ x) i = b i} ∧
      (A.submatrix (fun i : S => (i : Fin m)) id).rank = A.rank := by sorry

end CombOpt.TotalUnimodularity
