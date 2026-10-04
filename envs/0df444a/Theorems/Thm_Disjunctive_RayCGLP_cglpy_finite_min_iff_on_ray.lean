-- Prove2me | Theorems.Thm_Disjunctive_RayCGLP_cglpy_finite_min_iff_on_ray
-- name    : Disjunctive.RayCGLP.cglpy_finite_min_iff_on_ray
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:56:13.32238+00:00
-- url     : https://prove2.me/theorems/05466a13-4dae-4bb2-af5d-d313adaf510f
-- title:
--   Theorem 10.2 — (CGLP)_y has a finite minimum iff the ray meets P_D
-- statement:
--   This is Theorem 10.2 of Balas's *Disjunctive Programming*, cited to [32]: for the
--   ray-normalized cut-generating LP `(CGLP)_y` (eq. (10.9), `αy=1`), feasibility plus a finite
--   minimum of the objective `αx̄-β` is equivalent to the ray `{x̄+yλ : λ∈ℝ}` meeting `P_D`, the
--   convex hull of the disjunctive set being cut.
--
--   The book's proof: if `(CGLP)_y` is unbounded, there is a direction `(α̃,β̃)` of unboundedness with
--   `x̄ᵀα̃<β̃` and `yᵀα̃=0`, so `(x̄+yλ)ᵀα̃<β̃` for every `λ`, hence the ray never meets `P_D`.
--   Conversely, if the ray never meets `P_D`, a separating hyperplane `(α̂,β̂)` with `α̂y=0`,
--   `α̂x̄<β̂` gives a direction of unboundedness.
--
--   **Formalization Note.** `(CGLP)_y`'s feasibility is stated directly as validity of `(α,β)` for
--   `P_D` under the normalization `αy=1` (`IsCGLPYFeasible`), rather than through an explicit
--   multiplier/extreme-ray representation — matching how the theorem and its proof are themselves
--   phrased purely in terms of `(α,β)`-validity for `P_D`, not in terms of a specific disjunction's
--   multipliers.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 138, Theorem 10.2

import Mathlib
import Definitions.Def_Disjunctive_RayCGLP_Basic

namespace Disjunctive.RayCGLP

/-- Theorem 10.2 (Balas §10.6, p. 138, [32]): if `(CGLP)_y` is feasible, it has a finite minimum
if and only if `x̄+yλ ∈ P_D` for some `λ ∈ ℝ`. `P_D` is the closed convex hull of the disjunctive set, as on the page; the separation
argument of the proof needs it (`P_D = {(3,1), (3,-1)}`, `x̄ = 0`, `y = (1,0)` refutes the
statement for an arbitrary set). -/
theorem cglpy_finite_min_iff_on_ray {n : ℕ} (PD : Set (Fin n → ℝ)) (hPDconv : Convex ℝ PD)
    (hPDclosed : IsClosed PD) (y xbar : Fin n → ℝ)
    (hfeas : ∃ α β, IsCGLPYFeasible PD y α β) :
    CGLPYHasFiniteMin PD y xbar ↔ ∃ lam : ℝ, xbar + lam • y ∈ PD := by sorry

end Disjunctive.RayCGLP
