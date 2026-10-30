-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_masked_history_survival_additive_split
-- name    : AvramDividend.Classical.avram_ws01b_actual_masked_history_survival_additive_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:16:16.270443+00:00
-- url     : https://prove2.me/theorems/fe26f00d-0e27-4725-80c7-10d7dae1bb1a
-- title:
--   Actual continuous killed-survival horizon equals the shifted masked historical reserve event
-- statement:
--   For the real original Lévy path, continuous survival through s+T is pathwise equivalent to future interval survival with initial reserve x+X_s when the historical path survived and with negative sentinel reserve -1 otherwise. At future time zero, the negative sentinel excludes any ruined history. The exact identity is valid at reserve zero with positive BV W(0), so it supports a source killed Chapman–Kolmogorov law.
-- source:
--   Actual original Lévy path algebra, NNReal time addition, killed history mask. Inputs for WS1B all-horizon killed semigroup; no circular scale harmonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_ws01b_actual_masked_history_survival_additive_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (s T : ℝ≥0) (ω : Ω) :
    (∀ t : ℝ≥0, t ≤ s + T → 0 ≤ x + X.X t ω) ↔
    (∀ v : ℝ≥0, v ≤ T →
      0 ≤ (if ∀ w : ℝ≥0, w ≤ s → 0 ≤ x + X.X w ω
            then x + X.X s ω else (-1 : ℝ)) +
        (X.X (s + v) ω - X.X s ω)) := by sorry
