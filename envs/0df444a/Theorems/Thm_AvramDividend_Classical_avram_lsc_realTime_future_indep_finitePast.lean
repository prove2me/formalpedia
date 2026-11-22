-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_realTime_future_indep_finitePast
-- name    : AvramDividend.Classical.avram_lsc_realTime_future_indep_finitePast
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T15:35:43.775666+00:00
-- url     : https://prove2.me/theorems/5d978fa2-d389-40de-a906-de9125e8990a
-- title:
--   Original real-time Lévy increment independent of every finite vector of past observations
-- statement:
--   A centred and Gaussian-scaled real-time increment of Avram's original Lévy process is independent of the entire finite-dimensional vector of process observations made by the starting time. This strengthens single-increment independence into a finite-dimensional past statement useful for a Brownian-motion construction on the original probability space.
-- source:
--   Bridge for the original-space Brownian representation in Avram stopped Ito-Meyer proof, using canonical proved predecessor 8d9862cd-21d0-4741-98ee-a75a7b294b58 and native adaptedness of SpectrallyNegativeLevy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_lsc_realTime_centered_increment_indep_past
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_lsc_realTime_future_indep_finitePast
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {m : ℕ} (v : Fin m → ℝ≥0)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (hv : ∀ i, v i ≤ Real.toNNReal s) :
    Indep
      (MeasurableSpace.comap
        (fun ω : Ω => fun i : Fin m => X.X (v i) ω) inferInstance)
      (MeasurableSpace.comap (fun ω =>
        ((X.X (Real.toNNReal t) ω - X.X (Real.toNNReal s) ω) -
          (t - s) * X.c) / X.σ) inferInstance) P := by sorry
