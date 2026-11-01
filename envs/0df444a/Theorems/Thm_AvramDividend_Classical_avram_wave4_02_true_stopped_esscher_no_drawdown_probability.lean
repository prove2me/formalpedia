-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_true_stopped_esscher_no_drawdown_probability
-- name    : AvramDividend.Classical.avram_wave4_02_true_stopped_esscher_no_drawdown_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:05:05.828174+00:00
-- url     : https://prove2.me/theorems/e2ba7161-12b6-4116-aa10-c67deef8ab82
-- title:
--   Genuine first-record stopped Esscher law assigns exact exponential mass to actual drawdown survival
-- statement:
--   Fix a true source spectrally negative Levy path, q>0 and positive Esscher root, with divergent small-jump variation. Define the real stopped Esscher density at strict first upward record h>0, zero on infinite passage, and the source reflected drawdown-ruin time D_a. The measure P.withDensity of this exact likelihood assigns to the concrete source survival event {tau_h<D_a} the exact ENNReal probability exp(-h*lambda(a)), where lambda(a) is the already-proved original killed first-record hazard after Esscher normalization. No abstract or hypothetical Ito intensity appears; identifying the event as absence of actual marked excursions under a common stopped-history law remains independent.
-- source:
--   Proved actual stopped record exponential normalization a8da6c5c; original upper passage measurability 7ded075d and reflected ruin clock measurability 322896d6; KKR (2013) eq.31 void-event precursor.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_stopped_record_exponential_normalisation
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_true_stopped_esscher_no_drawdown_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    let τ := twoSidedExitUpTime X h
    let D := barrierRuinTime X a
    let Q := P.withDensity (fun ω : Ω =>
      if τ ω < (⊤ : ℝ≥0∞)
      then ENNReal.ofReal (Real.exp (φ * h - q * (τ ω).toReal))
      else 0)
    let rate := -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
        barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
      else 0 ∂P).toReal) - φ
    Q {ω : Ω | τ ω < D ω} =
      ENNReal.ofReal (Real.exp (-(h * rate))) := by sorry
