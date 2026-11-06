-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn9_original_stopped_physical_grid_times_measurable
-- name    : AvramDividend.Classical.avram_bv_env3_turn9_original_stopped_physical_grid_times_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:54:56.783723+00:00
-- url     : https://prove2.me/theorems/e38da324-6625-4052-88a9-aa4ff539940a
-- title:
--   Measurable original ruin-stopped physical-grid clocks
-- statement:
--   For each deterministic mesh and original admissible spectrally negative Lévy dividend strategy, every random physical-grid clock stopped at the minimum of ruin and finite horizon is measurable, and each clock remains bounded above by that stopped horizon. These are basic prerequisites for measurable original stopped-grid payoff and compensated-jump integrands.
-- source:
--   Original ruinTime_measurable (bbfbecf4, Proved) and NNReal/Borel min measurability, applied to exact stopped physical-grid clock shape in 1359bfd0 (Proved). Supports c1e2f021 stochastic signed Fatou grid construction, not a replacement for its jump compensation or expected drift proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn9_original_stopped_physical_grid_times_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (m : ℕ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → Ω → ℝ≥0 := fun j ω =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) (τ ω)
    (∀ j, Measurable (u j)) ∧ (∀ j ω, u j ω ≤ τ ω) := by sorry
