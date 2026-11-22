-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_original_filtered_brownian_exists
-- name    : AvramDividend.Classical.avram_lsc_zerojump_original_filtered_brownian_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T17:10:46.477312+00:00
-- url     : https://prove2.me/theorems/1df1cb31-2581-48c2-8298-c025addaaac9
-- title:
--   Same-original-space Brownian source and filtered stochastic-calculus interface for zero-jump Avram Lévy processes
-- statement:
--   For the original zero-jump Avram spectrally negative Lévy process with positive Gaussian coefficient, there exist on the original probability space both a LevyStochCalc BrownianMotion W and the real-indexed pullback of the original right-continuous filtration. W is Brownian relative to that filtration and is pointwise exactly the drift-centred and Gaussian-normalised original process. This bundles the verified representation and filtered-adaptation theorems into a direct entry point for the imported stopped Brownian Itô formula.
-- source:
--   Direct combination of Proved Avram original-space Brownian witness 05b01179-f449-4dd4-ab7a-ed44323d0879 and Proved original-space Brownian filtration theorem 2a260b0b-caa5-43ac-8917-ff05bcc10f8e, in service of Avram Dividend Classical mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43 and P4-F source fdb9a6a3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_original_sameSpace_brownian
import Theorems.Thm_AvramDividend_Classical_avram_lsc_sameSpace_brownian_filtered
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_lsc_zerojump_original_filtered_brownian_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ) :
    ∃ W : LevyStochCalc.Brownian.BrownianMotion P,
      ∃ ℱr : Filtration ℝ mΩ,
        (∀ t : ℝ, ℱr t = 𝓕.rightCont (Real.toNNReal t)) ∧
        LevyStochCalc.Brownian.IsBrownianFiltration W ℱr ∧
        (∀ (t : ℝ) (ω : Ω),
          W.W t ω =
            (X.X (Real.toNNReal t) ω - (Real.toNNReal t : ℝ) * X.c) / X.σ) := by sorry
