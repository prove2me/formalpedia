-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ruin_clipped_tail_inf_stopping_times
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_ruin_clipped_tail_inf_stopping_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:11:28.303043+00:00
-- url     : https://prove2.me/theorems/dae08fbd-1984-4610-8a6c-4d6acc3e1a75
-- title:
--   Tail-infimum of original ruin-clipped stopping clocks remains a genuine right-continuous stopping time
-- statement:
--   For the actual SpectrallyNegativeLevy P 𝓕 and an admissible dividend strategy D, let S_n be arbitrary genuine stopping times of the source right-continuous filtration, with no monotonicity or convergence assumptions. For every n, the tail-infimum clock inf_{k≥0} min(ruinTime,S_(n+k)) is still a genuine stopping time of 𝓕.rightCont, is measurable, and the sequence of these tail infima is pointwise monotone. This delivers a correct original-filtration monotone envelope for nonmonotone stochastic localisers without any smoothness, bounded-variation, Gaussian, or boundary assumption; in particular no artificial filtration or stopping-clock condition is added.
-- source:
--   Corrected core 429e17ca-5528-40b5-b593-7c03973d0706; reuse Proved genuine ruinTime stopping theorem and pinned Mathlib IsStoppingTime.iInf.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_ubv_original_ruin_clipped_tail_inf_stopping_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ n, IsStoppingTime 𝓕.rightCont (S n)) :
    (∀ n : ℕ, IsStoppingTime 𝓕.rightCont
      (fun ω => ⨅ k : ℕ,
        min (ruinTime X x D ω) (S (n + k) ω))) ∧
    (∀ n : ℕ, Measurable
      (fun ω => ⨅ k : ℕ,
        min (ruinTime X x D ω) (S (n + k) ω))) ∧
    (∀ ω, Monotone
      (fun n : ℕ => ⨅ k : ℕ,
        min (ruinTime X x D ω) (S (n + k) ω))) := by sorry
