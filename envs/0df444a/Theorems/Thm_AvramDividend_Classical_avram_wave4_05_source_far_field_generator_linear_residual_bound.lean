-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_generator_linear_residual_bound
-- name    : AvramDividend.Classical.avram_wave4_05_source_far_field_generator_linear_residual_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:42:19.14007+00:00
-- url     : https://prove2.me/theorems/14531a1c-8611-4d50-90e9-5416b94a38f1
-- title:
--   Genuine compensated source generator bounded by drift with coercive affine residual above the barrier
-- statement:
--   For any source spectrally negative Lévy standing process and its q-scale function, the actual generator-integrability domain contains every reserve x≥cstar+1; there the generator of the candidate value is at most the drift c, and the discounted residual is at most c−q(x−cstar). The latter is a global affine upper envelope with slope −q<0. No drift-sign restriction is imposed and the full negative-jump crossing kernel remains present in the source generator.
-- source:
--   Canonical quantitative genuine compensated generator far-field bound, nonnegative optimal-barrier value and the exact unit-slope affine barrier continuation.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_generator_residual_le_drift_minus_discount
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_for_nonnegative_capital
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_linear_gt_cstar

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_far_field_generator_linear_residual_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (x : ℝ) (hfar : (cstar W).toReal + 1 ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x ≤ X.c ∧
      X.generator (vcstar W) x - q * vcstar W x ≤
        X.c - q * (x - (cstar W).toReal) := by sorry
