-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_sameSpace_brownian_filtered
-- name    : AvramDividend.Classical.avram_lsc_sameSpace_brownian_filtered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T15:53:14.34035+00:00
-- url     : https://prove2.me/theorems/2a260b0b-caa5-43ac-8917-ff05bcc10f8e
-- title:
--   Original right-continuous Avram filtration makes same-space Brownian driver filtered
-- statement:
--   If W is a LevyStochCalc Brownian motion exactly equal to the original Avram source after centring and Gaussian normalisation on the same sample space, the real-indexed pullback of Avram's original right-continuous filtration is a Brownian filtration for W. In particular, W is adapted and its entire future increment sigma-algebra is independent of the source starting filtration. This discharges the filtered-driver input to LevyStochCalc Brownian Ito in the Avram stopped source decomposition.
-- source:
--   Bridge to fdb9a6a3 and 26396e12. Uses Proved Avram full shifted-future path independence c8fa0b62-902d-44cd-a066-e3e5ea5ac2bf, plus sameSpace Brownian witness 05b01179-f449-4dd4-ab7a-ed44323d0879 (proof pending).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Theorems.Thm_AvramDividend_Classical_avram_ja18h_original_future_path_indep_rightcont
open MeasureTheory ProbabilityTheory Set LevyStochCalc.Brownian AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_lsc_sameSpace_brownian_filtered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (hW : ∀ (t : ℝ) (ω : Ω),
      W.W t ω =
        (X.X (Real.toNNReal t) ω - (Real.toNNReal t : ℝ) * X.c) / X.σ) :
    ∃ ℱr : Filtration ℝ mΩ,
      (∀ t : ℝ, ℱr t = 𝓕.rightCont (Real.toNNReal t)) ∧
      LevyStochCalc.Brownian.IsBrownianFiltration W ℱr := by sorry
