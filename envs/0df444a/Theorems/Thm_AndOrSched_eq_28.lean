-- Prove2me | Theorems.Thm_AndOrSched_eq_28
-- name    : AndOrSched.eq_28
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:29.361025+00:00
-- url     : https://prove2.me/theorems/19004c0b-c051-4799-ab2b-89f74e07a451
-- title:
--   (28), p.26 — $\alpha\sum_{i\preceq b}p_i\le\tau_{l^\beta_b}$ (corrected: (5f) with $\tau_l\ge p_j$)
-- statement:
--   Let the instance have integer processing times, $\varepsilon'>0$, $x$ a feasible solution of LP (5), $0<\beta\le1$, $\alpha=\beta/\Delta$, and $\prec$ an order compatible with the keys $l^\alpha_a$ ($a\in A$), $l^\beta_b$ ($b\in B$). Then for every $b\in B$,
--   $$\alpha\sum_{i\preceq b}p_i\;\le\;\tau_{l^\beta_b},$$
--   where $\sum_{i\preceq b}p_i$ is the completion time of $b$ in the schedule of $\prec$.
--
--   Differences from the source:
--   - correction: (5f): x_jl ≥ 0 for l ∈ [L] with τ_{l−1} ≥ p_j (other variables absent) → x_jl ≥ 0 for all l ∈ [L], and x_jl = 0 when τ_l < p_j; reason: as printed LP (5) is infeasible for A = {a}, B = {b}, p_a = 2, p_b = 0, P(b) = {a}, E∧ = ∅, ε′ = 1/2 (τ = (1, 1, 1.5, 2.25), L = 3, no l has τ_{l−1} ≥ 2), although the instance has a feasible schedule; a job completing in (τ_{l−1}, τ_l] has p_j ≤ τ_l
--   - generalization: x̄ an optimal solution → x any feasible solution of LP (5); reason: the chain uses only (5c) and nonnegativity
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, (28), p.26

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_delta
import Definitions.Def_AndOrSched_listC
import Definitions.Def_AndOrSched_Compat
import Definitions.Def_AndOrSched_LP5Feasible
import Definitions.Def_AndOrSched_alphaPoint
import Definitions.Def_AndOrSched_key
import Definitions.Def_AndOrSched_tau
open scoped Classical NNReal

namespace AndOrSched

/-- Display (28), p.26 (Happach, Schulz, arXiv:2001.07011v1):
`α Σ_{i⪯b} pᵢ ≤ Σ_{i⪯b} η_i^b(β) pᵢ = Σ_{i⪯b} Σ_{k=1}^{l_b^β} pᵢ x̄_{ik} ≤ Σ_{i∈N} Σ_{k=1}^{l_b^β} pᵢ x̄_{ik} ≤ τ_{l_b^β}`.

Let the instance have integer processing times, `ε' > 0`, `x` a feasible solution of LP (5),
`β ∈ (0, 1]`, `α = β/Δ`, and `σ` an order compatible with the `α`-intervals of the `A`-jobs and the
`β`-intervals of the `B`-jobs. Then `α Σ_{i⪯b} pᵢ ≤ τ_{l_b^β}` for every `b ∈ B`, where
`Σ_{i⪯b} pᵢ` is the completion time of `b` in the schedule of `σ`. -/
theorem eq_28 (I : Instance) (hint : ∀ j, ∃ n : ℕ, I.p j = n) (ε' : ℝ) (hε' : 0 < ε')
    (x : I.N → ℕ → ℝ) (hx : LP5Feasible I ε' x) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (σ : I.N ≃ Fin (Fintype.card I.N)) (hσ : Compat I (key I x β) σ) (b : I.B) :
    β / (delta I : ℝ) * listC I σ (Sum.inr b) ≤ tau ε' (alphaPoint x (Sum.inr b) β) := by sorry

end AndOrSched
