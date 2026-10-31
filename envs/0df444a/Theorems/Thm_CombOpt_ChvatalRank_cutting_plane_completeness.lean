-- Prove2me | Theorems.Thm_CombOpt_ChvatalRank_cutting_plane_completeness
-- name    : CombOpt.ChvatalRank.cutting_plane_completeness
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:40.007372+00:00
-- url     : https://prove2.me/theorems/896ee070-4c21-47f6-a534-c9a935e3fe8f
-- title:
--   Theorem 6.31 (corrected: $P\neq\emptyset$ or $w$ a nonnegative combination of the rows) — completeness of cutting-plane proofs
-- statement:
--   Let $P=\{x : Ax\le b\}$ be a rational polytope and let $w^Tx\le t$ be an inequality, with $w$ integral, satisfied by all integral vectors in $P$. Suppose that $P\ne\emptyset$ or $w=y^TA$ for some $y\ge0$. Then there exists a cutting-plane proof of
--   $$
--   w^Tx\le t'
--   $$
--   from $Ax\le b$, for some $t'\le t$.
--
--   So every inequality with integral coefficients that holds for the integer points of a rational polytope is implied by a finite sequence of rounding steps.
--
--   Differences from the source:
--   - correction: no hypothesis beyond P being a rational polytope → additionally P ≠ ∅ or w = yᵀA with y ≥ 0; reason: the printed statement is false for empty P: A = [0], b = [−1], w = [1], t = 0 satisfies every assumption vacuously, but every derived inequality has zero left side, so w is never reached (machine-checked in the sanity file); the proof on p. 232 takes l = max {wᵀx : x ∈ P}, which needs P ≠ ∅; every nonempty P and w = 0 satisfy the added hypothesis, so Theorem 6.32 remains a special case
--   - reading: P = {x : Ax ≤ b} is a rational polytope → A and b are real and the set {x : Ax ≤ b} is a rational polytope; reason: the page calls the set P rational; a rational system Ax ≤ b is the special case
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 6.31, p. 230 (PDF 238)

import Mathlib
import Definitions.Def_RobustToDynamics_polyhedron
import Definitions.Def_CombOpt_ChvatalRank_IsCuttingPlaneProof
import Definitions.Def_CombOpt_ChvatalRank_IsRationalPolytope

open Matrix

namespace CombOpt.ChvatalRank

/-- **Theorem 6.31 (corrected).** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 6.31, p. 230 (PDF 238): "Let P = {x : Ax ≤ b} be a rational
polytope and let wᵀx ≤ t be an inequality, with w integral, satisfied by all integral vectors in P.
Then there exists a cutting-plane proof of wᵀx ≤ t′ from Ax ≤ b, for some t′ ≤ t."

**Formalization Note.** Correction: hypothesis `hw'`. As printed the theorem fails for an empty `P`
whose rows do not generate `w`: for `A = [0]`, `b = [-1]`, `w = [1]`, `t = 0` every derived inequality
has left side `0`, so `w` is never reached (`Solutions/verification/CombOpt_ChvatalRank_sanity`).
The book's proof takes `l = max {wᵀx : x ∈ P}`, which needs `P ≠ ∅`. `hw'` is exactly what is needed:
it holds for every nonempty `P`, and for `w = 0`, so Theorem 6.32 stays a special case.
`A`, `b` are real and only the set `P` is required to be a rational polytope. -/
theorem cutting_plane_completeness {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hP : IsRationalPolytope (RobustToDynamics.polyhedron A b))
    {w : Fin n → ℝ} {t : ℝ} (hw : IsIntegralVector w)
    (hvalid : ∀ x ∈ RobustToDynamics.polyhedron A b, IsIntegralVector x → w ⬝ᵥ x ≤ t)
    (hw' : (RobustToDynamics.polyhedron A b).Nonempty ∨ ∃ y : Fin m → ℝ, 0 ≤ y ∧ y ᵥ* A = w) :
    ∃ t' : ℝ, t' ≤ t ∧ IsCuttingPlaneProof A b w t' := by sorry

end CombOpt.ChvatalRank
