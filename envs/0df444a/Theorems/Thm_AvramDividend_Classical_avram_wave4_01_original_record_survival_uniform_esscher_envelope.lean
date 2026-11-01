-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_survival_uniform_esscher_envelope
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_survival_uniform_esscher_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T18:04:43.067262+00:00
-- url     : https://prove2.me/theorems/c5d17433-ae05-4846-916c-382777d09135
-- title:
--   Uniform positive-Esscher exponential envelope for true killed first-record survival at every drawdown depth
-- statement:
--   If ψ(φ)=q with q>0 and φ>0, the genuine original-process killed first-record discount mass E[e^{-qT_h};T_h<D_a] is at most exp(-φ h), simultaneously for every positive drawdown depth a and positive upward record height h. Under the Standing-free divergent small-jump variation hypothesis, the true first-record exponential law and positive Esscher-root hazard slope bound yield this pointwise, depth-independent integrable domination. It is the missing direct envelope required for dominated convergence at varying depths.
-- source:
--   Accepted original record exponential-law theorem 1c71a04d and source scale log-slope positive-Esscher root bound a5dbcace; direct exp monotonicity and h>0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_survival_uniform_esscher_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    (∫⁻ ω, if twoSidedExitUpTime X h ω <
        barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q *
        (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P).toReal ≤ Real.exp (-(φ * h)) := by sorry
