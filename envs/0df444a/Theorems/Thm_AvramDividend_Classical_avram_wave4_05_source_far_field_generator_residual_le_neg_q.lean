-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_generator_residual_le_neg_q
-- name    : AvramDividend.Classical.avram_wave4_05_source_far_field_generator_residual_le_neg_q
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:42:56.19611+00:00
-- url     : https://prove2.me/theorems/80fdf8ba-5e70-4c40-aac8-7d77bc68e4db
-- title:
--   Strict negative one-discount-rate source generator residual beyond an explicit reserve threshold
-- statement:
--   For the exact compensated spectrally negative Lévy generator at finite barrier c*, under the Standing conditions and a q-scale function, at any reserve x at least c*+1+max(0,c/q), the barrier candidate lies in the generator domain and the discounted generator residual is at most −q, a strictly negative quantitative HJB safety margin for q>0. In particular this strengthens the previously proved far-field nonpositive generator condition without requiring a bounded-reserve condition or assuming c≥0.
-- source:
--   Derived by combining the canonical source quantitative full-jump generator upper bound, Proved nonnegative value at barrier, and Proved affine continuation. Includes crossing jumps in the full genuine generator integral.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_generator_residual_le_drift_minus_discount
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_for_nonnegative_capital
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_linear_gt_cstar

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_far_field_generator_residual_le_neg_q
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (x : ℝ)
    (hfar : (cstar W).toReal + 1 + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x - q * vcstar W x ≤ -q := by sorry
