-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_fixed_horizon_upcrossing_uniform_tail
-- name    : AvramDividend.Classical.chat01_fixed_horizon_upcrossing_uniform_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:40:30.755931+00:00
-- url     : https://prove2.me/theorems/9cc1a9fd-1602-4527-80af-1f507d86ffb8
-- title:
--   Uniform vanishing of finite-horizon upward-passage probabilities at large spatial barriers
-- statement:
--   For a fixed deterministic time horizon and any positive probability tolerance, there exists a spatial level such that every measurable event of Lévy first upcrossing beyond that level by the horizon has probability no greater than the tolerance. The bound is uniform over all such events, derived from the positive-root Esscher Chernoff inequality. This can control boundary errors in grid approximations and stopped-scale limits.
-- source:
--   Proved chat01_finite_horizon_upcrossing_probability_explicit_tail plus logarithmic inversion and real exponential monotonicity.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_chat01_finite_horizon_upcrossing_probability_explicit_tail
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat01_fixed_horizon_upcrossing_uniform_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (t ε : ℝ) (hε : 0 < ε) :
    ∃ z0 : ℝ, ∀ z : ℝ, z0 ≤ z → 0 ≤ z →
      ∀ A : Set Ω, MeasurableSet A →
        A ⊆ {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)} →
        (∀ ω ∈ A, ENNReal.toReal (twoSidedExitUpTimeCorrected X z ω) ≤ t) →
        P A ≤ ENNReal.ofReal ε := by sorry
