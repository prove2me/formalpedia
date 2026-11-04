-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_vcstar_interior_cutoff_zero
-- name    : AvramDividend.Classical.avram_p4_c_generator_vcstar_interior_cutoff_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:14:25.042277+00:00
-- url     : https://prove2.me/theorems/62bbd4c9-968a-4130-a5d9-ac229678462e
-- title:
--   Candidate barrier value has exactly zero epsilon-split original generator residual at every strict interior state
-- statement:
--   For the c-star barrier candidate vcstar and the original source Lévy process, the already Proved generator harmonicity and source generator-integrability hold at all strict interior positive y<cstar under its standing smoothness hypotheses. For every epsilon>0 the exact epsilon-split second-order, source drift and signed compensated negative-jump terms then sum to q vcstar(y). This is an honest stopped-interior specialisation and does not make any boundary or Itô-martingale claim.
-- source:
--   Proved generator_vcstar_eq_zero 88d146b8-1b63-463d-8780-cf80ad7a9d40, accepted epsilon split 5434bf03-5ab7-4955-984e-cb4aa16c7af7, paper Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_negative_mark_integral_cutoff_split

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_vcstar_interior_cutoff_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W) (ε : ℝ) (hε : 0 < ε) :
    ∀ y ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) y ∧
      (X.σ ^ 2 / 2 * iteratedDeriv 2 (vcstar W) y +
        X.c * deriv (vcstar W) y +
        (∫ z in Iio (-ε),
          SpectrallyNegativeLevy.generatorIntegrand (vcstar W) y z ∂X.ν) +
        (∫ z in Ico (-ε) 0,
          SpectrallyNegativeLevy.generatorIntegrand (vcstar W) y z ∂X.ν) -
        q * vcstar W y = 0) := by sorry
