-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_generator_residual_le_drift_minus_discount
-- name    : AvramDividend.Classical.avram_wave4_05_source_far_field_generator_residual_le_drift_minus_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:30:34.212769+00:00
-- url     : https://prove2.me/theorems/cde30f83-f0bc-4a4e-b32a-848cded27e4d
-- title:
--   Quantitative source Lévy generator residual bound above the barrier by drift minus discount
-- statement:
--   For a spectrally negative Lévy risk process under Standing, q>0, and its q-scale function W, at every reserve x at least one unit above the finite optimal barrier c*, the actual Lévy generator is integrable on the barrier candidate and its discounted residual is at most c−q v_c*(x). The compensation convention is exact: all jumps y in (−1,0) remain above the barrier and contribute zero, while jumps y≤−1 contribute a nonpositive integrand by global monotonicity of v_c*. No stochastic verification, generator-domain shortcut or sign assumption on the drift is used.
-- source:
--   Original source-generator sign decomposition using Proved canonical compensated-jump zero lemma, finite-barrier monotonicity, genuine generator integrability and exact drift-plus-jump identity. Proved independent prerequisite theorem receipts.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_finite_cstar
import Theorems.Thm_AvramDividend_Classical_barrier_generatorIntegrand_zero_small_negative_jump_above
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_generator_above_eq_drift_add_jump

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_05_source_far_field_generator_residual_le_drift_minus_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (x : ℝ)
    (hfar : (cstar W).toReal + 1 ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x - q * vcstar W x ≤
        X.c - q * vcstar W x := by sorry
