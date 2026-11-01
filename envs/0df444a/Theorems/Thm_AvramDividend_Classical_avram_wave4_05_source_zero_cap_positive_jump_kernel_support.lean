-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_zero_cap_positive_jump_kernel_support
-- name    : AvramDividend.Classical.avram_wave4_05_source_zero_cap_positive_jump_kernel_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:26:43.295965+00:00
-- url     : https://prove2.me/theorems/43385c3f-b439-4fcc-894b-b607fc374c20
-- title:
--   The original source compensated zero-barrier jump kernel is nonpositive outside strict ruin crossing
-- statement:
--   For the genuine original compensated spectrally negative Levy generator, when the candidate optimal dividend barrier is zero, at every positive reserve x the generator integrand is nonpositive for every negative jump y outside the strict small ruin-crossing band -1<y<-x. For -1<y<0 with x+y>=0 the affine barrier value v(z)=z+v(0) for all nonnegative z gives exact compensation cancellation, including landing at zero. For y<=-1 the original generator does not compensate and monotonicity gives a nonpositive difference. No first Levy moment or Gaussian/BV/C2 hypothesis is introduced.
-- source:
--   Original Avram Palmowski Pistorius generator, canonically Proved barrierValue_zero_affine_nonnegative, vcstar_monotone_of_zero_cstar and original above-barrier affine derivative.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_zero_cap_positive_jump_kernel_support {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hc0 : cstar W = 0) (x : ℝ) (hx : 0 < x) (y : ℝ) (hy : y < 0) (houtside : y ∉ Ioo (-1 : ℝ) (-x)) : SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ≤ 0 := by sorry
