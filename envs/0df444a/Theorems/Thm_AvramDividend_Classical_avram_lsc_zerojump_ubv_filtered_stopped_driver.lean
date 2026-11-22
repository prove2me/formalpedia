-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_ubv_filtered_stopped_driver
-- name    : AvramDividend.Classical.avram_lsc_zerojump_ubv_filtered_stopped_driver
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T17:53:58.167565+00:00
-- url     : https://prove2.me/theorems/e72d0175-b6bd-45bf-ad30-0049fa7ed69a
-- title:
--   Avram original UBV zero-jump stopped surplus has a same-space filtered Brownian noise and stopping clock
-- statement:
--   Assume exactly the zero-jump unbounded-variation source hypotheses of the original Avram P4-F target and its right-continuous stopping time. Then on the same original probability space there exist a LevyStochCalc Brownian motion W and a compatible real-time filtration, with exact equality of W to the Gaussian-normalised original source process, with W adapted and independent of the entire future increment sigma-algebra as required by LevyStochCalc, and with the original ruin-truncated stopping time simultaneously a real-time stopping time. Derive the probability instance and positive Gaussian coefficient from the source instead of adding extra assumptions. The declared probability typeclass instance is supplied by the original SpectrallyNegativeLevy.isProbability field at every use.
-- source:
--   Proof bridge targeting AvramDividend.Classical.avram_p4_f4_zero_jump_source_reduction 683607b6, stopped Bochner Ito 26396e12 and public source fdb9a6a3. Combines Proved 37d963a0, 05b01179, 2a260b0b and 4360d638 at 0df444a360eaa60ab8c11dca51a86af692955474. Source-facing application may synthesize the explicitly named IsProbabilityMeasure P from X.isProbability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_zero_levy_ubv_sigma_pos
import Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_original_sameSpace_brownian
import Theorems.Thm_AvramDividend_Classical_avram_lsc_sameSpace_brownian_filtered
import Theorems.Thm_AvramDividend_Classical_avram_lsc_nnreal_stopping_to_real_clock
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_lsc_zerojump_ubv_filtered_stopped_driver
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∃ W : LevyStochCalc.Brownian.BrownianMotion P,
      ∃ ℱr : Filtration ℝ mΩ,
        (∀ t : ℝ, ℱr t = 𝓕.rightCont (Real.toNNReal t)) ∧
        LevyStochCalc.Brownian.IsBrownianFiltration W ℱr ∧
        (∀ (t : ℝ) (ω : Ω),
          W.W t ω =
            (X.X (Real.toNNReal t) ω - (Real.toNNReal t : ℝ) * X.c) / X.σ) ∧
        IsStoppingTime ℱr
          (fun ω => ((τ ω : ℝ) : WithTop ℝ)) := by sorry
