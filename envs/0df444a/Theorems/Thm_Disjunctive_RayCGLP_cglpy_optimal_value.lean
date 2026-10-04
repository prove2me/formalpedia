-- Prove2me | Theorems.Thm_Disjunctive_RayCGLP_cglpy_optimal_value
-- name    : Disjunctive.RayCGLP.cglpy_optimal_value
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:57:15.096931+00:00
-- url     : https://prove2.me/theorems/d060a1ee-326d-4632-b729-8d279e4c6282
-- title:
--   Theorem 10.3 — the optimal value of the ray-normalized CGLP
-- statement:
--   This is Theorem 10.3 of Balas's *Disjunctive Programming*, the goal theorem of this
--   mission, cited to [32]: if `(CGLP)_y` has an optimal solution `(α̃,β̃)`, its optimal value equals
--   the distance `λ*` one must travel from `x̄` along the ray `y` to reach `P_D`, and the resulting
--   point `x̄+yλ*` lies exactly on the optimal hyperplane.
--
--   $$
--   \bar x^T\tilde\alpha - \tilde\beta = \lambda^* := \min\{\lambda : \bar x+y\lambda \in
--   P_D\}, \qquad (\bar x+y\lambda^*)^T\tilde\alpha = \tilde\beta.
--   $$
--
--   The book's proof fixes `λ0` with `(x̄+yλ0)ᵀα̃=β̃` (using `α̃y≠0`, from the normalization `α̃y=1`)
--   and shows `λ0=λ*` by contradiction in both directions: if `λ0>λ*`, the point `x̄+yλ*` would
--   violate the optimal cut, contradicting `x̄+yλ*∈P_D`; if `λ0<λ*`, a separating hyperplane at `λ*`
--   would give a strictly better `(CGLP)_y` objective value than `(α̃,β̃)`, contradicting its
--   optimality.
--
--   **Formalization Note.** `IsCGLPYOptimal` bundles feasibility (validity for `P_D` plus `αy=1`) and
--   minimality of the objective `αx̄-β` over the feasible region, matching the theorem's own "has an
--   optimal solution" hypothesis directly; `λ*:=min{λ:x̄+yλ∈P_D}` is formalized via `sInf`, matching
--   the series' convention for a book-asserted minimum whose attainment is not independently
--   re-derived in the formal statement.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 138, Theorem 10.3

import Mathlib
import Definitions.Def_Disjunctive_RayCGLP_Basic

namespace Disjunctive.RayCGLP

/-- Theorem 10.3 (Balas §10.6, p. 138, [32]), the goal theorem of this mission: if `(CGLP)_y` has
an optimal solution `(α̃,β̃)`, then `x̄ᵀα̃ - β̃ = -λ*` with `λ* := min{λ : x̄ + yλ ∈ P_D}`, and
`(x̄ + yλ*)ᵀα̃ = β̃`.

The page's display prints `x̄ᵀα̃ - β̃ = λ*`; its own proof computes `x̄ᵀα̃ - β̃ = -λ₀` and then
`λ₀ = λ*`, so the sign of the proof is the one taken here (`P_D = {(3,t) : |t| ≤ 1}`, `x̄ = 0`,
`y = (1,0)` has optimum `α = (1,0)`, `β = 3`, hence `αx̄ - β = -3` while `λ* = 3`). `λ*` is a
*minimum*, and `P_D` a closed convex set, as on the page: for `P_D = {(3,1), (3,-1)}` the set of
`λ` is empty and a real infimum of the empty set would read `0`. -/
theorem cglpy_optimal_value {n : ℕ} (PD : Set (Fin n → ℝ)) (hPDconv : Convex ℝ PD)
    (hPDclosed : IsClosed PD) (y xbar : Fin n → ℝ)
    (alphaT : Fin n → ℝ) (betaT : ℝ) (hopt : IsCGLPYOptimal PD y xbar alphaT betaT)
    (lamStar : ℝ) (hlam : IsLeast {lam : ℝ | xbar + lam • y ∈ PD} lamStar) :
    dotProduct alphaT xbar - betaT = -lamStar ∧
      dotProduct alphaT (xbar + lamStar • y) = betaT := by sorry

end Disjunctive.RayCGLP
