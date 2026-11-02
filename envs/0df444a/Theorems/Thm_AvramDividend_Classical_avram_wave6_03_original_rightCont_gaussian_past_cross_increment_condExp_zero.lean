-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_past_cross_increment_condExp_zero
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_past_cross_increment_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:46:52.082052+00:00
-- url     : https://prove2.me/theorems/6deb01cc-26db-43c5-a055-ee755f05fa0a
-- title:
--   Actual zero-jump Gaussian past times future increment is L1 and conditionally zero
-- statement:
--   For an arbitrary original SpectrallyNegativeLevy P F with nu=0 (no positive-sigma hypothesis), the original centred past value Ms=X.X_s-s*c times the actual source drift-centred future increment Y=X.X_t-X.X_s-(t-s)c is integrable and has conditional expectation zero given original right-continuous F_s. Prove both factors are genuine MemLp 2 by specialising already Proved original bounded-stopped Gaussian L2 at constant stops 0 and s; use the pinned MemLp.integrable_mul (Holder Cauchy-Schwarz) and condExp_mul_of_stronglyMeasurable_left, the source adaptedness of Ms, and already Proved original deterministic conditional mean-zero for Y. This gives the true cross term for a future compensated-square Gaussian martingale on the same Omega and original path; it is not a bracket for nu nonzero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_past_cross_increment_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (s t : ℝ≥0) (hst : s ≤ t) :
    let Ms : Ω → ℝ := fun ω => X.X s ω - (s : ℝ) * X.c
    let Y : Ω → ℝ := fun ω => X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    Integrable (Ms * Y) P ∧
      (P[Ms * Y | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ))) := by
  sorry
