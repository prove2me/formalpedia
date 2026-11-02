-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_variance
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:34:01.742586+00:00
-- url     : https://prove2.me/theorems/ee48aad4-1cb8-4c70-b178-dabda6b8d48a
-- title:
--   Original zero-jump Gaussian increment has exact deterministic conditional variance in right-continuous source history
-- statement:
--   The actual original SpectrallyNegativeLevy X with nu=0, for deterministic s<=t in the original right-continuous filtration, has a drift-centred increment Y which is in L2, and its true integrable square has conditional expectation (t-s)*sigma^2 given F.rightCont s. Apply already Proved original bounded stopped Gaussian L2, exact stopped source variance, independent source increments and the Mathlib conditional-expectation independence theorem. This includes sigma=0 without division. It supplies the conditional second-moment input for constructing the pure Gaussian compensated square martingale, but does not by itself construct a continuous bracket for general nonzero jump measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_indepIncrements_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_variance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (s t : ℝ≥0) (hst : s ≤ t) :
    let Y : Ω → ℝ := fun ω => X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    Integrable (fun ω => Y ω ^ 2) P ∧
      (P[(fun ω => Y ω ^ 2) | 𝓕.rightCont s] =ᵐ[P]
         (fun _ => ((t - s) : ℝ) * X.σ ^ 2)) := by
  sorry
