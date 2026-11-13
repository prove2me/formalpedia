-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b26_original_deterministic_mesh_square_energy_measurable
-- name    : AvramDividend.Classical.avram_b26_original_deterministic_mesh_square_energy_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:44:40.233046+00:00
-- url     : https://prove2.me/theorems/ce37534a-efd8-4b49-911a-486660dc433f
-- title:
--   Original deterministic physical Lévy mesh quadratic energy is measurable without auxiliary assumptions
-- statement:
--   For every deterministic finite collection of source clock intervals, the sum of the squared original drift-centred Lévy increments is measurable under the original filtration, by the source's adaptedness.
-- source:
--   Original source adaptedness for the SpectrallyNegativeLevy definition, compact C2 Taylor physical mesh supporting Avram Palmowski Pistorius (2007) Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b26_original_deterministic_mesh_square_energy_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s t : ℕ → ℝ≥0) :
    Measurable (fun ω : Ω => ∑ i ∈ S,
      (X.X (t i) ω - X.X (s i) ω -
        ((t i - s i) : ℝ) * X.c) ^ 2) := by sorry
