-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_actual_record_esscher_stopped_history_consistency
-- name    : AvramDividend.Classical.avram_wave4_02_actual_record_esscher_stopped_history_consistency
-- status  : Open
-- author  : @WillR
-- created : 2026-11-01T01:15:03.824497+00:00
-- url     : https://prove2.me/theorems/37d72263-309d-4e14-b3fe-2428f66b0feb
-- title:
--   Actual finite-record Esscher probabilities agree on the genuine earlier stopped history
-- statement:
--   The source first-record stopped Esscher probabilities Q_h and Q_H at levels 0<h<H restrict to the same law on every actual event observable at the earlier first-record time. The exact stopped-history measurability hypothesis is expressed against the given Levy filtration. This is a needed projective-consistency bridge for constructing actual locally cut-off reflected-excursion marks and ultimately an Ito excursion height compensator. No global tilted path law, Poisson mark process, or hypothetical characteristic measure is assumed. The proof must use genuine source strong Markov at an uncapped first record, no positive overshoot, and the accepted first-passage transform; those are NOT discharged by the proposed target statement.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2013), section 2.3, and Bertoin, Levy Processes IV; Proved source first-passage Laplace transform 0da3763f and normalized stopped Esscher probability 9d43bdb3. Requires uncapped stopped-history strong Markov passage factor.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_uncapped_record_esscher_probability

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_actual_record_esscher_stopped_history_consistency
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (h H : ℝ) (hh : 0 < h) (hH : h < H)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s]
        (A ∩ {ω : Ω | twoSidedExitUpTimeCorrected X h ω ≤ (s : ℝ≥0∞)})) :
    (P.withDensity (fun ω : Ω =>
      if twoSidedExitUpTimeCorrected X h ω < (⊤ : ℝ≥0∞)
      then ENNReal.ofReal (Real.exp
        (φ * h - q * (twoSidedExitUpTimeCorrected X h ω).toReal))
      else 0)) A =
    (P.withDensity (fun ω : Ω =>
      if twoSidedExitUpTimeCorrected X H ω < (⊤ : ℝ≥0∞)
      then ENNReal.ofReal (Real.exp
        (φ * H - q * (twoSidedExitUpTimeCorrected X H ω).toReal))
      else 0)) A := by sorry
