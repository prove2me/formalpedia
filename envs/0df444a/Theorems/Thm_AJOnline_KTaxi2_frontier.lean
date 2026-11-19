-- Prove2me | Theorems.Thm_AJOnline_KTaxi2_frontier
-- name    : AJOnline.KTaxi2.frontier
-- status  : Open
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:40:49.382847+00:00
-- url     : https://prove2.me/theorems/3ee725d1-4518-4d1a-9718-26476c97c129
-- title:
--   No memoryless 2-taxi policy is competitive as an AJ behaviour strategy
-- statement:
--   For every memoryless 2-taxi policy $A$, every labelled start $x_0\in\mathbb R^2$, every $\rho\ge1$ and every $b\ge0$, the behaviour strategy $\beta_A$ is **not** $(\rho,b)$-randomised-competitive on the 2-taxi game from $x_0$. That is, some finite request script gives
--   $$\mathbb E[\mathrm{alg}]>\rho\,\mathbb E[\mathrm{opt}]+b .$$
--
--   By the bridge, this statement is equivalent to the platform's `KTaxi.Competitive.Supplement.theorem_1_3`.
-- source:
--   AJ form of C. Coester, Y. Huang, T.-Y. Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Theorem 1.3, PDF p. 23 (printed p. 22)

import Mathlib
import Definitions.Def_AJOnline_KTaxi2

namespace AJOnline.KTaxi2

open AJGames KTaxi.Competitive.Supplement
open scoped ENNReal NNReal

/-- **Frontier: no memoryless 2-taxi policy is competitive, as an AJ behaviour strategy.** Open. It
reduces to the platform's open `KTaxi.Competitive.Supplement.theorem_1_3` through
`competitive_transfer` (see the sketch). AJ axioms used: none beyond the definitions. -/
theorem frontier (A : MemorylessPolicy) (x₀ : Fin 2 → ℝ) (ρ b : ℝ≥0) (hρ : 1 ≤ ρ) :
    ¬ RandCompetitive (costed x₀) (behOf A x₀) ρ b := by sorry

end AJOnline.KTaxi2
