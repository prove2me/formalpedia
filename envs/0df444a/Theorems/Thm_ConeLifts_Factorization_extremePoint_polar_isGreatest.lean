-- Prove2me | Theorems.Thm_ConeLifts_Factorization_extremePoint_polar_isGreatest
-- name    : ConeLifts.Factorization.extremePoint_polar_isGreatest
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:44:47.623579+00:00
-- url     : https://prove2.me/theorems/6dbbdeba-1e67-4044-92fa-df4cd5a6dae4
-- title:
--   Theorem 2.4, proof, p. 4 — every extreme point $c$ of $C^\circ$ has $\max_{x\in C}\langle c,x\rangle = 1$
-- statement:
--   Let $n \ge 1$, let $C \subseteq \mathbb R^n$ be a convex body, and let $c$ be an extreme point of the polar $C^\circ$. Then the linear functional $x \mapsto \langle c, x\rangle$ attains the value $1$ on $C$ and never exceeds it:
--
--   $$
--   \max\{\langle c, x\rangle : x \in C\} = 1 .
--   $$
--
--   In the proof of Theorem 2.4 this fixes the optimal value of the conic program over the lift from which the factor $B(c)$ is read off.
--
--   **Formalization Note** The maximum is stated with `IsGreatest`, so attainment is part of the claim. The hypothesis $n \ge 1$ is the paper's implicit full-dimensionality: in $\mathbb R^0$ the only point is $0$ and the maximum is $0$.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 4, Theorem 2.4 (proof)

import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Shared_polar

open scoped InnerProductSpace

namespace ConeLifts.Factorization

/-- Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, Theorem 2.4, proof, p. 4: for an extreme point
`c` of `C°`, `max{⟨c, x⟩ : x ∈ C} = 1` (the maximum is attained). The hypothesis `1 ≤ n` is the
paper's implicit "full-dimensional convex body in ℝⁿ"; for `n = 0` the maximum is `0`. -/
theorem extremePoint_polar_isGreatest {n : ℕ} (hn : 1 ≤ n)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (c : EuclideanSpace ℝ (Fin n)) (hc : c ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C)) :
    IsGreatest ((fun x => ⟪c, x⟫_ℝ) '' C) 1 := by sorry

end ConeLifts.Factorization
