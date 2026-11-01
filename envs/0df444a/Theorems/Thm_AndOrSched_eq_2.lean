-- Prove2me | Theorems.Thm_AndOrSched_eq_2
-- name    : AndOrSched.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:30:28.26787+00:00
-- url     : https://prove2.me/theorems/49156186-50c8-493c-9d3d-55a4157e1f74
-- title:
--   (2), p.8 — $\int_0^1 t^\gamma_j\,d\gamma\le\bar C_j$
-- statement:
--   For every feasible solution $x$ of LP (1) and every job $j$, the map $\gamma\mapsto t^\gamma_j$ is integrable on $(0,1]$ and
--   $$\int_0^1 t^\gamma_j\,d\gamma\;\le\;\sum_{t=1}^{T}x_{jt}\cdot t=\bar C_j .$$
--
--   Differences from the source:
--   - generalization: x̄ an optimal solution → x any feasible solution of LP (1); reason: the chain uses only (1b) and (1f)
--   - encoding: the display ∫ … = Σ … ≤ … = C̄_j → integrability on (0, 1] and the inequality between the two ends; reason: the integrability clause makes the bound non-vacuous; the intermediate equalities are proof steps
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, (2), p.8

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_LP1Feasible
import Definitions.Def_AndOrSched_fracC1
import Definitions.Def_AndOrSched_alphaPoint
open scoped Classical NNReal

namespace AndOrSched

/-- Display (2), p.8 (Happach, Schulz, arXiv:2001.07011v1): `∫₀¹ tⱼ^γ dγ ≤ Σ_{t=1}^{T} x̄_{jt} · t = C̄ⱼ`.

For every feasible solution `x` of LP (1) and every job `j`, the function `γ ↦ tⱼ^γ` is integrable on
`(0, 1]` and its integral is at most the fractional completion time `C̄ⱼ`. -/
theorem eq_2 (I : Instance) (x : I.N → ℕ → ℝ) (hx : LP1Feasible I x) (j : I.N) :
    MeasureTheory.IntegrableOn (fun γ : ℝ => (alphaPoint x j γ : ℝ)) (Set.Ioc 0 1) ∧
    ∫ γ in Set.Ioc (0 : ℝ) 1, (alphaPoint x j γ : ℝ) ≤ fracC1 I x j := by sorry

end AndOrSched
