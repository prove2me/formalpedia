-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_ruin_crossing_generatorIntegrand_eq_neg_value
-- name    : AvramDividend.Classical.avram_wave4_05_source_ruin_crossing_generatorIntegrand_eq_neg_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:55:14.129122+00:00
-- url     : https://prove2.me/theorems/45c66621-4866-4de4-a2e6-4a68b1dd4986
-- title:
--   Exact full source generator integrand for Lévy jumps crossing strictly below ruin
-- statement:
--   Let v=vcstar W be the actual piecewise barrier candidate with zero extension below reserve zero. At x≥cstar(W)+1, for every negative jump y satisfying x+y<0, the genuine spectrally negative Lévy generatorIntegrand is exactly −v(x). This includes the compensation convention: such a ruin-crossing jump necessarily has y≤−1, so there is no small-jump compensation, and its post-jump value vanishes by the source zero-reserve branch. No stochastic assumption, Lévy moment condition or smoothness is needed.
-- source:
--   Accepted original source exact far-field compensated kernel theorem, source barrierValue zero extension, and arithmetic x≥cstar+1≥1.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_generatorIntegrand_far_field_exact_large_jump_kernel

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_ruin_crossing_generatorIntegrand_eq_neg_value
    (W : ℝ → ℝ) (x y : ℝ)
    (hfar : (cstar W).toReal + 1 ≤ x)
    (hruin : y < -x) :
    SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y =
      -vcstar W x := by sorry
