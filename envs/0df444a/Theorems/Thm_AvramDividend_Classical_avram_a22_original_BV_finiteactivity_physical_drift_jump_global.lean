-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_BV_finiteactivity_physical_drift_jump_global
-- name    : AvramDividend.Classical.avram_a22_original_BV_finiteactivity_physical_drift_jump_global
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T13:30:32.741638+00:00
-- url     : https://prove2.me/theorems/40ca0651-c5da-4d3b-9b9b-440150e8e17c
-- title:
--   Original finite-activity BV drift and physical left-jump series decomposition on one global all-time event
-- statement:
--   Upgrade the Proved exact original BV drift-minus-source-jump physical path identity at each bounded strictly positive horizon to one common full-probability event for ALL nonnegative times. Take countable integer horizons, intersect their probability-one events and use a natural-number majorant for each t. This is a same-source real path result essential for uncompensated/compensated original Lévy–Itô identification, without any independent noise.
-- source:
--   Proved dcda0213-3cd9-45c6-a14c-b1fa3026d85d, exact physical BV jump drift decomposition on bounded horizons; Mathlib Filter.eventually_all; Kyprianou finite-activity Levy-Ito.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva22_original_finite_activity_standing_exact_drift_jump_path
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a22_original_BV_finiteactivity_physical_drift_jump_global
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (t : ℝ) * X.drift - X.X t ω =
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by sorry
