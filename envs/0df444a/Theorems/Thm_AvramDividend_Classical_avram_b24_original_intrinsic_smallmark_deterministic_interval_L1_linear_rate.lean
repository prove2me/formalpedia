-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_intrinsic_smallmark_deterministic_interval_L1_linear_rate
-- name    : AvramDividend.Classical.avram_b24_original_intrinsic_smallmark_deterministic_interval_L1_linear_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:44:43.298369+00:00
-- url     : https://prove2.me/theorems/80cc0cc9-d8ed-4039-9e1e-18768102d13c
-- title:
--   Any original finite-activity intrinsic compensated smallmark increment has a deterministic L1 physical interval rate
-- statement:
--   For any original finite-negative-jump-activity Lévy X and arbitrary same-space intrinsic compensated small-negative-mark process Jsmall satisfying its all-time a.e. residual witness, every fixed deterministic physical interval s≤t on which its increment is integrable has its expected absolute increment bounded sharply by the authentic original marked Poisson expected count ((t-s)ν((-1,0))).toReal plus elapsed time times the absolute full smallmark compensator first moment. The bound uses the exact source pathwise true smallmark Poisson interval inequality, real marked-count Campbell intensity and original probability law. In particular it gives quantitative L1 continuity of intrinsic Jsmall as t↓s, independently of any large negative jump moment or artificial postruin source.
-- source:
--   B24 actual original Jsmall physical interval Poisson domination plus exact original negative Borel interval real marked count first moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_intrinsic_smallmark_deterministic_interval_L1_linear_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (s t : ℝ≥0) (hst : s ≤ t)
    (hJI : Integrable (fun ω => Jsmall t ω - Jsmall s ω) P) :
    (∫ ω, ‖Jsmall t ω - Jsmall s ω‖ ∂P) ≤
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Ioo (-1 : ℝ) 0)).toReal +
      ((t : ℝ) - (s : ℝ)) *
        ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖ := by sorry
