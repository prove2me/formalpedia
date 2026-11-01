-- Prove2me | Theorems.Thm_AndOrSched_eq_27
-- name    : AndOrSched.eq_27
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:37.12508+00:00
-- url     : https://prove2.me/theorems/b45bbe25-29a1-447c-b952-6255f8ddab7f
-- title:
--   (27), p.26 — $\int_0^1\tau_{l^\gamma_j-1}\,d\gamma\le\bar C_j$ (corrected: (5f) with $\tau_l\ge p_j$)
-- statement:
--   For every $\varepsilon'>0$, every feasible solution $x$ of LP (5) and every job $j$, the map $\gamma\mapsto\tau_{l^\gamma_j-1}$ is integrable on $(0,1]$ and
--   $$\int_0^1\tau_{l^\gamma_j-1}\,d\gamma\;\le\;\sum_{l=1}^{L}x_{jl}\,\tau_{l-1}=\bar C_j .$$
--
--   Differences from the source:
--   - correction: (5f): x_jl ≥ 0 for l ∈ [L] with τ_{l−1} ≥ p_j (other variables absent) → x_jl ≥ 0 for all l ∈ [L], and x_jl = 0 when τ_l < p_j; reason: as printed LP (5) is infeasible for A = {a}, B = {b}, p_a = 2, p_b = 0, P(b) = {a}, E∧ = ∅, ε′ = 1/2 (τ = (1, 1, 1.5, 2.25), L = 3, no l has τ_{l−1} ≥ 2), although the instance has a feasible schedule; a job completing in (τ_{l−1}, τ_l] has p_j ≤ τ_l
--   - generalization: x̄ an optimal solution → x any feasible solution of LP (5); reason: the chain uses only (5b) and nonnegativity
--   - encoding: the display ∫ … = Σ … ≤ … = C̄_j → integrability and the inequality between the two ends; reason: the integrability clause makes the bound non-vacuous
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, (27), p.26

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_LP5Feasible
import Definitions.Def_AndOrSched_fracC5
import Definitions.Def_AndOrSched_alphaPoint
import Definitions.Def_AndOrSched_tau
open scoped Classical NNReal

namespace AndOrSched

/-- Display (27), p.26 (Happach, Schulz, arXiv:2001.07011v1): `∫₀¹ τ_{lⱼ^γ − 1} dγ ≤ Σ_{l=1}^{L} x̄_{jl} · τ_{l−1} = C̄ⱼ`.

For every `ε' > 0`, every feasible solution `x` of LP (5) and every job `j`, the function
`γ ↦ τ_{lⱼ^γ − 1}` is integrable on `(0, 1]` and its integral is at most `C̄ⱼ`. -/
theorem eq_27 (I : Instance) (ε' : ℝ) (hε' : 0 < ε') (x : I.N → ℕ → ℝ) (hx : LP5Feasible I ε' x)
    (j : I.N) :
    MeasureTheory.IntegrableOn (fun γ : ℝ => tau ε' (alphaPoint x j γ - 1)) (Set.Ioc 0 1) ∧
    ∫ γ in Set.Ioc (0 : ℝ) 1, tau ε' (alphaPoint x j γ - 1) ≤ fracC5 I ε' x j := by sorry

end AndOrSched
