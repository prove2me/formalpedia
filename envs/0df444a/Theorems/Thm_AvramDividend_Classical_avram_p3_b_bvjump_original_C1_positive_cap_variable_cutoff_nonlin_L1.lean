-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_C1_positive_cap_variable_cutoff_nonlin_L1
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_C1_positive_cap_variable_cutoff_nonlin_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:36:52.294115+00:00
-- url     : https://prove2.me/theorems/62eadbc2-bb6f-47d0-8f36-928918071c0d
-- title:
--   Original BV C1 positive-cap verification value has finite nonlinear Levy source small-jump L1
-- statement:
--   The P3 verification theorem's actual C1 positive-cap value-function hypothesis and source process bounded variation imply that nonlinear small original Levy marks are integrable for any source cutoff and compact interior controlled reserve. The local Lipschitz envelope is derived from smoothness rather than assumed.
-- source:
--   Proved P3-B original source BV variable-cutoff nonlinear L1 and Mathlib compact C1 Lipschitz

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_BV_variable_cutoff_nonlin_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_C1_positive_cap_variable_cutoff_nonlin_L1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (a b δ u : ℝ) (ha : 0 < a) (hb : ENNReal.ofReal b < C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hu : u ∈ Icc (a + δ) b) : IntegrableOn (fun z : ℝ => w (u + z) - w u) (Ioo (-δ) 0) X.ν := by sorry
