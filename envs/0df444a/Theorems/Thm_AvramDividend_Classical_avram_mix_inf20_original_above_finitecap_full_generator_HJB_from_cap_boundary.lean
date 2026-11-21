-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_above_finitecap_full_generator_HJB_from_cap_boundary
-- name    : AvramDividend.Classical.avram_mix_inf20_original_above_finitecap_full_generator_HJB_from_cap_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:27:26.989407+00:00
-- url     : https://prove2.me/theorems/e693f3d5-2a46-4fb7-9e0a-e7398c531c8a
-- title:
--   True original Lévy finitecap above barrier generator HJB inherits negative drift from cap boundary and full mark integral comparison
-- statement:
--   Original finite-cap caplinear Lévy generator verification above the barrier: for any actual spectrally negative Lévy process, q≥0 and premark reserve y>b, an explicit cap-boundary HJB generator inequality together with an explicitly stated monotonicity estimate on the full negative Lévy mark generator integral implies (X.generator V y)-qV(y)≤0. The generator at y reduces exactly to drift plus integral of its true generatorIntegrand by server-Proved 771f63e9. The affine potential V(y)=w(b)+(y-b) makes the extra -q(y-b) nonpositive. Crucially, the monotonicity of the full mark integral is retained as a genuine hypothesis rather than invented from the pointwise compensated sign, which alone does not control heavy-tail or boundary effects; proving it is the remaining original stochastic analytic obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_above_finitecap_full_generator_reduces_to_drift_jump
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_above_finitecap_full_generator_HJB_from_cap_boundary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (b y q : ℝ)
    (hy : b < y) (hq : 0 ≤ q)
    (hBoundary : X.c +
      (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun t => if t ≤ b then w t else w b + (t - b)) b z
        ∂X.ν) - q * w b ≤ 0)
    (hBActual : (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun t => if t ≤ b then w t else w b + (t - b)) y z
        ∂X.ν) ≤
        (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun t => if t ≤ b then w t else w b + (t - b)) b z
        ∂X.ν)) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ b then w t else w b + (t - b)
    X.generator V y - q * V y ≤ 0 := by sorry
