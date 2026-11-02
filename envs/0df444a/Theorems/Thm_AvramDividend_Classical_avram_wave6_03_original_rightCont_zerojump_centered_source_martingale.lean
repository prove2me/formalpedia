-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:40:43.743458+00:00
-- url     : https://prove2.me/theorems/0e0e6523-99f7-4178-b236-3c7328c51eaf
-- title:
--   The actual zero-jump Lévy source drift-centred path is a right-continuous-filtration martingale
-- statement:
--   Given an arbitrary original SpectrallyNegativeLevy P F with ν=0 and any Gaussian coefficient σ≥0 including σ=0, the same original centred path M_t=X.X_t-tc is a true martingale in the original right-continuous filtration F.rightCont. Use the Proved genuine conditional zero-mean source Gaussian increment at deterministic s≤t (with L1), original adaptedness to show strong measurability, the no-jump source increment integrability at time s, and Mathlib condExp_add and condExp_of_stronglyMeasurable to obtain the conditional expectation equality. The source paths, Ω, P and filtration remain original; this theorem establishes the martingale property but does not identify the pathwise continuous component for ν≠0 or the bracket of a general jump-bearing source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) :
    Martingale (fun t ω => X.X t ω - (t : ℝ) * X.c) 𝓕.rightCont P := by
  sorry
