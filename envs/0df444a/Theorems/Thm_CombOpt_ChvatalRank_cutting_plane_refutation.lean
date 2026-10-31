-- Prove2me | Theorems.Thm_CombOpt_ChvatalRank_cutting_plane_refutation
-- name    : CombOpt.ChvatalRank.cutting_plane_refutation
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:25.814851+00:00
-- url     : https://prove2.me/theorems/cf30f209-5a5d-4ee3-8fd4-b7ec92fda7a2
-- title:
--   Theorem 6.32 — a rational polytope with no integral vectors has a cutting-plane proof of $0^Tx\le-1$
-- statement:
--   Let $P=\{x : Ax\le b\}$ be a rational polytope that contains no integral vectors. Then there exists a cutting-plane proof of
--   $$
--   0^Tx\le-1
--   $$
--   from $Ax\le b$.
--
--   This is the integer analogue of Farkas' Lemma, which certifies emptiness of $P$ by a nonnegative combination of the inequalities.
--
--   Differences from the source:
--   - reading: P = {x : Ax ≤ b} is a rational polytope → A and b are real and the set {x : Ax ≤ b} is a rational polytope; reason: the page calls the set P rational, and the book defines this as having some rational defining system; a rational system Ax ≤ b is the special case
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 6.32, p. 230 (PDF 238)

import Mathlib
import Definitions.Def_RobustToDynamics_polyhedron
import Definitions.Def_CombOpt_ChvatalRank_IsCuttingPlaneProof
import Definitions.Def_CombOpt_ChvatalRank_IsRationalPolytope

open Matrix

namespace CombOpt.ChvatalRank

/-- **Theorem 6.32.** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 6.32, p. 230 (PDF 238): "Let P = {x : Ax ≤ b} be a rational polytope
that contains no integral vectors. Then there exists a cutting-plane proof of 0ᵀx ≤ −1 from Ax ≤ b."

**Formalization Note.** `A`, `b` are real and only the set `P` is required to be a rational polytope;
a rational system is the special case. `P` may be empty. -/
theorem cutting_plane_refutation {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hP : IsRationalPolytope (RobustToDynamics.polyhedron A b))
    (hno : ∀ x ∈ RobustToDynamics.polyhedron A b, ¬ IsIntegralVector x) :
    IsCuttingPlaneProof A b 0 (-1) := by sorry

end CombOpt.ChvatalRank
