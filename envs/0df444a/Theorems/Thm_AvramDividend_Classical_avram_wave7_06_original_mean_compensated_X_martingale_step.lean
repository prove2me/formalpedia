-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_mean_compensated_X_martingale_step
-- name    : AvramDividend.Classical.avram_wave7_06_original_mean_compensated_X_martingale_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:06:02.551221+00:00
-- url     : https://prove2.me/theorems/95664068-391e-43d4-b9ab-ab3d58584f99
-- title:
--   Canonical source Levy process minus original mean is a true filtration martingale step
-- statement:
--   For genuine X and original P and 𝓕, if X_s and X_t are integrable, the mean-compensated original X_(s+t) has conditional expectation X_s-E[X_s] given 𝓕_s. The proof combines original X conditional expectation given its past, original mean additivity and pinned condExp_sub/condExp_const. This is the true scalar original-process compensated martingale step; it is distinct from a jump-band marked-Poisson compensated martingale.
-- source:
--   W7-06 source original-process compensation martingale precursor for stopped jump integrals.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_mean_compensated_X_martingale_step
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hStart : Integrable (X.X s) P)
    (hFuture : Integrable (X.X t) P) :
    P[(fun ω => X.X (s + t) ω -
      (∫ η, X.X (s + t) η ∂P)) | 𝓕 s] =ᵐ[P]
      (fun ω => X.X s ω - (∫ η, X.X s η ∂P)) := by sorry
