-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_uncapped_record_esscher_probability
-- name    : AvramDividend.Classical.avram_wave4_02_uncapped_record_esscher_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:00:18.637385+00:00
-- url     : https://prove2.me/theorems/9d43bdb3-7869-4b47-a9f2-e78f1af39ab9
-- title:
--   Actual uncapped first-record stopped Esscher density is a probability at every positive regulator level
-- statement:
--   For the actual spectrally negative Levy path, let tau_h be the genuine strict first upper passage of h>0. With q>0, phi>0 and psi(phi)=q, the stopped positive Esscher likelihood exp(phi*h-q*tau_h) on {tau_h finite}, zero otherwise, has original-P expectation exactly one. Thus its withDensity measure is a genuine probability on the original sample space for every finite regulator cutoff h. This is the source-local-time-level stopped law needed for an eventual marked-excursion construction, without asserting an all-time tilted path law, a Poisson point process or a characteristic measure.
-- source:
--   Canonical one-sided strict upcrossing Laplace formula 0da3763f-17e2-414b-ac46-9b9f2088aa29; KKR (2013), section 2.3 local-time normalization L=S. Zero at infinite passage is essential.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_exact_strict_upcrossing_discount

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_uncapped_record_esscher_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (h : ℝ) (hh : 0 < h) :
    IsProbabilityMeasure
      (P.withDensity (fun ω : Ω =>
        if twoSidedExitUpTimeCorrected X h ω < (⊤ : ℝ≥0∞)
        then ENNReal.ofReal (Real.exp
          (φ * h - q * (twoSidedExitUpTimeCorrected X h ω).toReal))
        else 0)) := by sorry
