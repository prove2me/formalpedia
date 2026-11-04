-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finite_NNReal_ruin_clocks_monotone_sup_actual_ruin
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_finite_NNReal_ruin_clocks_monotone_sup_actual_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:00:27.307663+00:00
-- url     : https://prove2.me/theorems/3a5c7721-1c54-4401-be15-187972c29c7e
-- title:
--   Exact original finite NNReal ruin clocks increase to actual possibly infinite ruin time
-- statement:
--   The actual original ruin-truncated NNReal clocks, defined at every integer horizon, are monotone and their ENNReal supremum is exactly the original ruinTime, whether finite or infinite. This gives genuine temporal exhaustion at the source process and filtration without spatial cap-exit assumptions. It makes no convergence claim about stochastic integrals or dividends.
-- source:
--   Original source τ equation from P4-F 0dda1be7-9d8b-41e0-ae51-55fab5c38e22; ENNReal.coee_toNNReal finite round-trip and ENNReal.iSup_natCast.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact finite NNReal truncations exhaust actual original controlled ruin, including infinity. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_finite_NNReal_ruin_clocks_monotone_sup_actual_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ n ω, τ n ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    (∀ ω, Monotone (fun n => τ n ω)) ∧
      (∀ ω, (⨆ n : ℕ, (τ n ω : ℝ≥0∞)) = ruinTime X x D ω) := by sorry
