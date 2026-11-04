-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_vcstar_original_cutoff_zero
-- name    : AvramDividend.Classical.avram_p4_c_generator_vcstar_original_cutoff_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:51:20.125817+00:00
-- url     : https://prove2.me/theorems/184f6a7f-6207-4d77-94bb-3e823ff86a33
-- title:
--   The optimal barrier candidate has zero original epsilon-physical-drift generator residual throughout its strict positive interior
-- statement:
--   For the original Lévy process X, its q-scale function W and vcstar barrier candidate, assume the already Proved source generator harmonicity hypotheses and strict 0<epsilon<1. Then at every y∈(0,cstar), vcstar is generator-integrable and the full physical cutoff drift c−∫_{-1<z<-epsilon}zν, Gaussian correction, two uncompensated large-jump integrals and exact compensated small-jump integral sum to q*vcstar(y). This is source-backed equality to zero, no terminal/boundary extension or stopped martingale assertion.
-- source:
--   Proved generator_vcstar_eq_zero 88d146b8-1b63-463d-8780-cf80ad7a9d40 and P4-C full original epsilon drift identification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_vcstar_original_cutoff_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ y ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) y ∧
      (X.σ ^ 2 / 2 * iteratedDeriv 2 (vcstar W) y +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv (vcstar W) y +
        (∫ z in Iic (-1 : ℝ), vcstar W (y + z) - vcstar W y ∂X.ν) +
        (∫ z in Ioo (-1 : ℝ) (-ε), vcstar W (y + z) - vcstar W y ∂X.ν) +
        (∫ z in Ico (-ε) 0,
          SpectrallyNegativeLevy.generatorIntegrand (vcstar W) y z ∂X.ν) -
        q * vcstar W y = 0) := by sorry
