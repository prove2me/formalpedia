-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps10_poisson_power_integrable
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps10_poisson_power_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:48:16.422405+00:00
-- url     : https://prove2.me/theorems/b0a020bb-f079-499e-b293-d2febf9407fe
-- title:
--   Every real exponential power is integrable under a finite Poisson count law
-- statement:
--   The pure Poisson exponential-moment integrability needed after proving the genuine original finite-band count law. This is the directly ported absolute-convergence argument from MathFin PoissonPgf; no claims about constructing Avram's Poisson measure or infinite-activity jumps.

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

open Classical MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps10_poisson_power_integrable (r : ℝ≥0) (a : ℝ) :
    Integrable (fun n : ℕ => a ^ n) (poissonMeasure r) := by sorry
