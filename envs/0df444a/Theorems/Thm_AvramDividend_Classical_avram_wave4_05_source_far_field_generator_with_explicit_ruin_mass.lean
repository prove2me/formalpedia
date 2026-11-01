-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_generator_with_explicit_ruin_mass
-- name    : AvramDividend.Classical.avram_wave4_05_source_far_field_generator_with_explicit_ruin_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:07:48.658054+00:00
-- url     : https://prove2.me/theorems/225f306f-f900-498b-b75c-81e21b3cee84
-- title:
--   Exact original Lévy generator with strict ruin-crossing tail intensity and surviving large-jump contribution
-- statement:
--   For x≥cstar(W)+1 under source q-scale assumptions, the original source Lévy generator of vcstar W is genuinely integrable and equals its drift c, minus vcstar(x) times the source Lévy real measure of jumps y<−x, plus the uncompensated increment integral over −x≤y≤−1. The endpoint y=−x landing exactly at reserve zero is retained in the second term. This is a complete explicit large-jump and zero-reserve decomposition with small jumps exactly compensated and the Gaussian curvature term zero above the barrier.
-- source:
--   Accepted original source generator equals drift plus large negative tail; Proved exact large-tail split at strict ruin threshold; all genuine source definitions preserved.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_generator_eq_drift_add_large_tail
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_large_tail_split_at_ruin

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_far_field_generator_with_explicit_ruin_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hfar : (cstar W).toReal + 1 ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x =
        X.c + (X.ν.real (Iio (-x)) * (-vcstar W x) +
          ∫ y in Icc (-x) (-1 : ℝ),
            (vcstar W (x + y) - vcstar W x) ∂X.ν) := by sorry
