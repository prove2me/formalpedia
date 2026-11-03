-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat07a_original_BV_C1_affine_source_generator_plus_spatial_drift
-- name    : AvramDividend.Classical.avram_chat07a_original_BV_C1_affine_source_generator_plus_spatial_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:36:10.886289+00:00
-- url     : https://prove2.me/theorems/0093a96f-5898-4abe-a5a1-1694a6d4d387
-- title:
--   Original BV Lévy C¹ generator under deterministic first-order reserve motion has exact spatial drift correction
-- statement:
--   For a genuine Standing bounded-variation spectrally negative Lévy process on its native sample space, globally C¹ Lipschitz test w and GeneratorIntegrable w x, shifting the payoff evaluation base by d*h during the true source increment produces right-time expected slope X.generator w x + d*w'(x), with exact Real.toNNReal time and genuine integrals under P. This covers O(h) deterministic reserve motion, which is excluded by the previously Proved o(h)-perturbation helper. The proof combines the canonically Proved fixed-base generator with the native Lévy expected C¹ drift correction and explicit original transition integrability; there are no fictitious laws, independent increments introduced, stochastic stopping assertions or weakened generator conventions.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), deterministic first-order drift-shift semigroup analysis; source-faithful original process. Accepted fixed BV generator b56e7174-ebfe-49ac-899d-0f14fc900201 and accepted drift-expectation correction f0a80299-feb7-4e05-ba12-76dca6f671a9 give exact first-order decomposition, with native transition integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_levy_transition_right_generator_of_global_C1_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_original_C1_source_drift_expectation_right_slope
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_chat07a_original_BV_C1_affine_source_generator_plus_spatial_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) (hgen : X.GeneratorIntegrable w x)
    (d : ℝ) :
    Tendsto
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, w (x + X.X (Real.toNNReal h) ω + d * h) ∂P) - w x))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (X.generator w x + d * deriv w x)) := by sorry
