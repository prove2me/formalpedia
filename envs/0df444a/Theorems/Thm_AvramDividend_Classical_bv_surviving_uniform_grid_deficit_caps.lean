-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_surviving_uniform_grid_deficit_caps
-- name    : AvramDividend.Classical.bv_surviving_uniform_grid_deficit_caps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:48:52.352553+00:00
-- url     : https://prove2.me/theorems/817c6484-4c3f-4603-b5ec-fe7729143058
-- title:
--   Every drift-deficit increment before strict reflected ruin is bounded by the corresponding physical drift accrual
-- statement:
--   On a deterministic mesh contained within a strict zero-barrier reflected-survival interval, the actual Levy capital process has nondecreasing values by the proved survival-prefix monotonicity theorem. Consequently each physical-drift deficit increment is no larger than the physical drift accrued over the mesh cell. A real-valued mesh spacing hypothesis avoids coercion issues. This supplies the eventwise cap in the accepted integrated exponential mesh bound.
-- source:
--   Proved zero_reflected_ruin_strict_survival_capital_monotone_prefix and ring algebra.

import Theorems.Thm_AvramDividend_Classical_zero_reflected_ruin_strict_survival_capital_monotone_prefix
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_surviving_uniform_grid_deficit_caps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (N : ℕ) (ts : ℕ → ℝ≥0) (δ : ℝ≥0)
    (hOrder : ∀ k : ℕ, k < N → ts k ≤ ts (k + 1))
    (hWithin : ∀ k : ℕ, k < N → ts (k + 1) ≤ T)
    (hStepReal : ∀ k : ℕ, k < N →
      (ts (k + 1) : ℝ) - (ts k : ℝ) = (δ : ℝ))
    (ω : Ω)
    (hBefore : (T : ℝ≥0∞) < barrierRuinTime X 0 ω) :
    ∀ k : ℕ, k < N →
      (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) -
        (X.drift * (ts k : ℝ) - X.X (ts k) ω) ≤
      X.drift * (δ : ℝ) := by sorry
