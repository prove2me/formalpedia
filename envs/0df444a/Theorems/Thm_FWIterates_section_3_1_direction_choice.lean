-- Prove2me | Theorems.Thm_FWIterates_section_3_1_direction_choice
-- name    : FWIterates.section_3_1_direction_choice
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:25:10.472957+00:00
-- url     : https://prove2.me/theorems/818db36e-126e-46c0-96a5-75689908fa8a
-- title:
--   §3.1, p.6 — the directions $u_k$ can be chosen in the admissible cones, orthogonal to the previous step
-- statement:
--   For the sketches $\mathcal P_k$ and points $B_k,C_k$ of §3.1 there are unit vectors $(u_k)_{k\in\mathbb N}$ with $u_0\in\mathcal K_{\mathcal P_0}C_0$ and, for all $k\ge1$,
--   $$
--   \begin{cases}u_k\in\mathcal K_{\mathcal P_k}C_k\text{ and }\langle C_k-B_{k-1},u_k\rangle=0&\text{if $k$ is even;}\\ u_k\in\mathcal K_{\mathcal P_k}B_k\text{ and }\langle B_k-C_{k-1},u_k\rangle=0&\text{if $k$ is odd;}\end{cases}
--   $$
--   moreover every $u_k$ lies in the interior of the normal cone $\mathcal N_{\mathcal P_k}V_k$, where $V_k=C_k$ for even $k$ and $V_k=B_k$ for odd $k$.
--
--   These are the directions prescribed to Theorem 3.1 in Counterexample 3.5: the gradient at the current vertex is orthogonal to the next Frank-Wolfe step, which makes exact line search stop at the next vertex (Lemma 3.3).
--
--   Differences from the source:
--
--   - generalization: u_k ∈ K_{P_k}C_k (k even), u_k ∈ K_{P_k}B_k (k odd), u₀ ∈ K_{P₀}C₀ → additionally u_k ∈ int N_{P_k}V_k for every k; reason: a stronger existence claim; dropping the interior clause gives the page's statement, and the corrected Theorem 3.1 needs it
--   - encoding: (u_k) the directions of Theorem 3.1, (u_k) ∈ S^ℕ → ‖u k‖ = 1 inside IsDirectionChoice; reason: the u_k are the unit vectors of Theorem 3.1
-- source:
--   Bolte, Combettes & Pauwels, The Iterates of the Frank-Wolfe Algorithm May Not Converge, arXiv:2202.08711v1, §3.1, p.6, display "The construction allows to choose (uk)k∈N such that …"

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone
import Definitions.Def_FWIterates_sketchPoints

open scoped RealInnerProductSpace Pointwise

namespace FWIterates

/-- **The choice of the directions `(u_k)` in §3.1** (arXiv:2202.08711v1, §3.1, display "The
construction allows to choose (uk)", p.6). There are unit vectors `(u_k)` with `u₀ ∈ K_{P₀}C₀` and,
for all `k ≥ 1`, `u_k ∈ K_{P_k}C_k` and `⟨C_k − B_{k−1}, u_k⟩ = 0` if `k` is even, and
`u_k ∈ K_{P_k}B_k` and `⟨B_k − C_{k−1}, u_k⟩ = 0` if `k` is odd (`IsDirectionChoice`); moreover
each `u_k` lies in the **interior of the normal cone** `N_{P_k}V_k` (`V_k = C_k` for even `k`, `B_k`
for odd `k`).

**Formalization Note** The interior clause is stronger than the page and is what the corrected
hypothesis (i) of Theorem 3.1 (`IsSketch`) requires. -/
theorem section_3_1_direction_choice :
    ∃ u : ℕ → EuclideanSpace ℝ (Fin 2), IsDirectionChoice u ∧
      ∀ k, u k ∈ interior
        (FirstOrderOpt.ConvexTheory.normalCone (sketchPolygon k) (sketchVertex k)) := by sorry

end FWIterates
