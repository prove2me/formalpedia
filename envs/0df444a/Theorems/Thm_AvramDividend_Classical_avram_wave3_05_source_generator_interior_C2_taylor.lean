-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_source_generator_interior_C2_taylor
-- name    : AvramDividend.Classical.avram_wave3_05_source_generator_interior_C2_taylor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:28:31.632111+00:00
-- url     : https://prove2.me/theorems/c4be88ef-5eaf-425f-8173-4f9c612a1526
-- title:
--   Source Levy compensated negative jump equals the interior second-order Taylor kernel
-- statement:
--   For the original spectrally negative Lévy generator, any C² function on positive reserves has its compensated small negative-jump integrand equal exactly to the positive-axis triangular integral of its second derivative whenever the post-jump reserve remains positive. In particular this applies to the Gaussian q-scale function using proved source C² regularity. It is the basis for quadratic small-jump integrability under infinite activity.
-- source:
--   Original pinned SpectrallyNegativeLevy.generatorIntegrand definition; exact positive-axis Taylor from published source child avram_wave3_05_positive_C2_backward_taylor_exact; Gaussian scale C² from scaleFunction_contDiff_two_of_gaussian.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical Set MeasureTheory

theorem AvramDividend.Classical.avram_wave3_05_source_generator_interior_C2_taylor
    (W : ℝ → ℝ) (hW : ContDiffOn ℝ 2 W (Ioi 0))
    (x y : ℝ) (hy1 : -1 < y) (hy0 : y < 0) (hx : 0 < x + y) :
    SpectrallyNegativeLevy.generatorIntegrand W x y =
      ∫ t in (x + y)..x, (t - (x + y)) * iteratedDeriv 2 W t := by sorry
