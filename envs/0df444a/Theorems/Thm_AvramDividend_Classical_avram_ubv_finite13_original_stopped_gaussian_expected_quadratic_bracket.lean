-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_gaussian_expected_quadratic_bracket
-- name    : AvramDividend.Classical.avram_ubv_finite13_original_stopped_gaussian_expected_quadratic_bracket
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:27:34.30428+00:00
-- url     : https://prove2.me/theorems/2f5720cf-4f39-4ff2-a490-a96bf574b548
-- title:
--   Original stopped Gaussian increment energy equals the sampled quadratic bracket without extra clock hypotheses
-- statement:
--   For the same zero-jump original Gaussian Lévy source at two ordered bounded sampled stopping indices, the expected squared stopped increment is the expected increase of its stopped sampled quadratic-variation clock. Integrability of each sampled clock follows automatically from stopped-value integrability under the bounded stopping indices.
-- source:
--   Public Proved stopped source L2 de80c263, stopped increment variance difference 4489c8e9, stopped Q mean equality 46667cb1, and prospective pointwise stopped Q decomposition 773a5847. The pinned integrable_stoppedValue theorem supplies deterministic sampled bracket integrability directly, with no extra hypotheses.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_bounded_stopped_gaussian_L2_integrability
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_gaussian_increment_second_moment_difference
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_gaussian_compensated_square_mean
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_gaussian_Q_pointwise_decomposition

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite13_original_stopped_gaussian_expected_quadratic_bracket
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (grid : ℕ → ℝ≥0) (hgrid : Monotone grid)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (grid i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (hgrid hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (grid i) } : Filtration ℕ mΩ))
    (α β : Ω → WithTop ℕ)
    (hα : IsStoppingTime 𝓖 α) (hβ : IsStoppingTime 𝓖 β)
    (hαβ : α ≤ β)
    (N : ℕ) (hbounded : ∀ ω, β ω ≤ (N : WithTop ℕ)) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
    let A := stoppedValue (fun i : ℕ => M (grid i)) α
    let B := stoppedValue (fun i : ℕ => M (grid i)) β
    let TA := stoppedValue (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) α
    let TB := stoppedValue (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) β
    (∫ ω, (B ω - A ω)^2 ∂P) = (∫ ω, TB ω ∂P) - (∫ ω, TA ω ∂P) := by sorry
