-- Prove2me | Theorems.Thm_Disjunctive_RayCGLP_ray_normalization_geometry
-- name    : Disjunctive.RayCGLP.ray_normalization_geometry
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:56:45.570828+00:00
-- url     : https://prove2.me/theorems/819a90d0-8807-4034-8047-fc1da8ab285a
-- title:
--   Corollary 10.4 — the ray-normalized optimum as a supporting hyperplane of P_Q
-- statement:
--   This is Corollary 10.4 of Balas's *Disjunctive Programming*, cited to [32],
--   illustrated by the book's Fig. 10.3: taking `y:=x*-x̄` for a point `x*∈P_Q`, `(CGLP)_y` has an
--   optimal solution `(α̃,β̃)` with `α̃x̄<β̃`, and `α̃x=β̃` is the supporting hyperplane of `P_Q` that
--   meets the segment `(x̄,x*]` at the point closest to `x*`.
--
--   **Corrects a source typo.** The printed corollary reads "Let `y:=x̄` for some `x*∈P_Q`," which
--   omits "`x*-`" before "`x̄`" — confirmed against the figure caption immediately following it,
--   "Fig. 10.3 `y = x*-x̄`," which gives the intended formula unambiguously. See
--   `MODERATION_NOTES.md`.
--
--   **Formalization Note.** `P_D` (used to define `(CGLP)_y`) and `P_Q` (whose supporting hyperplane
--   the conclusion describes) are kept as two independent `Set (Fin n→ℝ)` parameters, per `BRIEF.md`'s
--   explicit warning not to conflate them; no relationship between them is asserted. "The point
--   closest to `x*`" on the segment `(x̄,x*]` is formalized as the *greatest* parameter `t∈(0,1]`
--   (`t=1` being `x*` itself) at which the hyperplane meets the line through `x̄,x*`, via
--   `IsGreatest`.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 139, Corollary 10.4

import Mathlib
import Definitions.Def_Disjunctive_RayCGLP_Basic

namespace Disjunctive.RayCGLP

/-- Corollary 10.4 (Balas §10.6, p. 139, [32]): for `y := x*-x̄` with `x*∈P_Q`, `(CGLP)_y` (defined
w.r.t. `P_D`) has an optimal solution `(α̃,β̃)` such that (i) `α̃x̄<β̃`, and (ii) `α̃x=β̃` is a
supporting hyperplane of `P_Q` whose intersection with the line through `x̄,x*` at parameter
`t∈(0,1]` (i.e. the point `x̄+t(x*-x̄)`, `t=1` being `x*` itself) is the greatest such `t` —
matching "the point closest to `x*`" on the segment `(x̄,x*]`.

**Corrects a source typo** (confirmed against the figure caption "Fig. 10.3 `y = x*-x̄`" in the
same section, immediately following this corollary): the printed corollary reads "`y:=x̄` for some
`x*∈P_Q`," omitting "`x*−`" before "`x̄`"; see `MODERATION_NOTES.md`. On the page `P_Q` and `P_D` are the same set, `cl conv F`; carrying them as two unrelated
parameters leaves the supporting-hyperplane claim about a set the optimum knows nothing of. -/
theorem ray_normalization_geometry {n : ℕ} (PD : Set (Fin n → ℝ)) (hPDconv : Convex ℝ PD)
    (hPDclosed : IsClosed PD) (xbar xstar : Fin n → ℝ)
    (hxstar : xstar ∈ PD) :
    ∃ alphaT betaT, IsCGLPYOptimal PD (xstar - xbar) xbar alphaT betaT ∧
      dotProduct alphaT xbar < betaT ∧ (∀ x ∈ PD, betaT ≤ dotProduct alphaT x) ∧
      ∃ t : ℝ, IsGreatest
        {t' : ℝ | t' ∈ Set.Ioc (0 : ℝ) 1 ∧
          dotProduct alphaT (xbar + t' • (xstar - xbar)) = betaT} t := by sorry

end Disjunctive.RayCGLP
