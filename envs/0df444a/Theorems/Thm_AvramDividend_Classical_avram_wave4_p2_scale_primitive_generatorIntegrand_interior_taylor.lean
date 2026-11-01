-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_generatorIntegrand_interior_taylor
-- name    : AvramDividend.Classical.avram_wave4_p2_scale_primitive_generatorIntegrand_interior_taylor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:35:33.154267+00:00
-- url     : https://prove2.me/theorems/a91a303e-1634-42ab-9056-63ab2a55854a
-- title:
--   Exact source primitive interior compensated generator Taylor kernel
-- statement:
--   For the actual source q-scale W under Standing, its positive C2 primitive U has the genuine compensated generator increment U(x-r)-U(x)+rU'(x) on each strictly interior small negative jump 0<r<min(1,x). It equals the exact second-order backward Taylor integral from x-r to x with nonnegative triangular weight (t-(x-r)) times the second derivative of U. This is the source-specific interior counterpart to the accepted zero-crossing strip estimate, enabling the O(r^2) weighted x-integral bound from the Proved generic tent theorem.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4 source Levy generator; accepted primitive C2 925aaf62, generic Taylor remainder 4ffca760, reflected source kernel 87cd84ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_scale_primitive_generatorIntegrand_interior_taylor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (r x : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hrx : r < x) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun z : ℝ => ∫ s in (0 : ℝ)..z, W s) x (-r) =
      ∫ t in (x-r)..x, (t - (x-r)) *
        iteratedDeriv 2 (fun z : ℝ => ∫ s in (0 : ℝ)..z, W s) t := by sorry
