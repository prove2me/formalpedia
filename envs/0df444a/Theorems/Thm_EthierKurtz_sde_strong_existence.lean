-- Prove2me | Theorems.Thm_EthierKurtz_sde_strong_existence
-- name    : EthierKurtz.sde_strong_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T05:55:00.174209+00:00
-- url     : https://prove2.me/theorems/90f983cc-4515-4ed3-8bad-3e44be7244d3
-- title:
--   Theorem 3.11 — strong existence with locally Lipschitz coefficients
-- statement:
--   Locally bounded Borel coefficients with the source one-sided growth and local Lipschitz bounds admit a solution for every fixed Brownian driver and independent square-integrable initial variable on the given probability space.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 5, Section 3, Theorem 3.11, printed p. 300 (PDF p. 309), equations (3.34)–(3.35); conventions printed pp. 276, 280, 282–283, 286, 290–291.

import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_EthierKurtz_IsStandardBrownian

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- Strong existence, Chapter 5 Theorem 3.11. Growth is one-sided for the drift;
there is no global Lipschitz, boundedness, or time-continuity assumption.
The probability space, Brownian driver and initial variable remain fixed. -/
theorem sde_strong_existence
    (P : Measure Ω) [IsProbabilityMeasure P]
    (σ : ℝ≥0 × SDEState d → SDEDiffusion d)
    (b : ℝ≥0 × SDEState d → SDEState d)
    (hσmeas : Measurable σ) (hbmeas : Measurable b)
    (hlocal : ∀ K : Set (ℝ≥0 × SDEState d), IsCompact K →
      ∃ C : ℝ, ∀ z ∈ K, ‖σ z‖ ≤ C ∧ ‖b z‖ ≤ C)
    (hgrowth : ∀ T : ℝ≥0, 0 < T → ∃ K : ℝ, ∀ t : ℝ≥0, t ≤ T →
      ∀ x : SDEState d, ‖σ (t, x)‖ ^ 2 ≤ K * (1 + ‖x‖ ^ 2) ∧
        inner ℝ x (b (t, x)) ≤ K * (1 + ‖x‖ ^ 2))
    (hlip : ∀ T : ℝ≥0, 0 < T → ∀ n : ℕ, 1 ≤ n → ∃ K : ℝ,
      ∀ t : ℝ≥0, t ≤ T → ∀ x y : SDEState d,
        ‖x‖ ≤ n → ‖y‖ ≤ n →
        max ‖σ (t, x) - σ (t, y)‖ ‖b (t, x) - b (t, y)‖ ≤ K * ‖x - y‖)
    (W : ℝ≥0 → Ω → SDEState d) (hW : IsStandardBrownian P W)
    (ξ : Ω → SDEState d) (hξmeas : Measurable ξ)
    (hindep : IndepFun ξ (fun ω t => W t ω) P)
    (hsecond : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) :
    ∃ X : ℝ≥0 → Ω → SDEState d, SolvesBrownianSDE P σ b W ξ X := by sorry
