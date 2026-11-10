-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_sampled_stop_gaussian_energy_lintegral
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_original_sampled_stop_gaussian_energy_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:19:39.36163+00:00
-- url     : https://prove2.me/theorems/e916b990-1286-490f-93e6-2b0ec2d83eb3
-- title:
--   Original Gaussian two sampled stops nonnegative quadratic energy bound
-- statement:
--   Under the precise original X.X zero-jump Gaussian sampled stopping-time hypotheses, convert the pre-existing ordinary second-moment bracket inequality (9954ba8b) into an actual nonnegative Lebesgue energy bound. Proved de80c263 supplies genuine L2 integrability, preventing the ordinary integral from silently equalling zero for a non-integrable function. This interface is needed by the two-sided physical-clock Fatou theorem for cap contact and the final stop-straddling cell.
-- source:
--   Proved 9954ba8b, de80c263; Mathlib ofReal_integral_eq_lintegral_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_bounded_stopped_gaussian_L2_integrability
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_two_sampled_stops_gaussian_gap_L2

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_original_sampled_stop_gaussian_energy_lintegral
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
    (N : ℕ) (hbounded : ∀ ω, β ω ≤ (N : WithTop ℕ))
    (ε : ℝ)
    (hTimeA : Integrable (stoppedValue
      (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) α) P)
    (hTimeB : Integrable (stoppedValue
      (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) β) P)
    (hGap : ∀ ω,
      stoppedValue
          (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) β ω -
        stoppedValue
          (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) α ω
        ≤ ε * X.σ ^ 2) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c
    let A := stoppedValue (fun i : ℕ => M (grid i)) α
    let B := stoppedValue (fun i : ℕ => M (grid i)) β
    (∫⁻ ω, ENNReal.ofReal ((B ω - A ω) ^ 2) ∂P) ≤
      ENNReal.ofReal (ε * X.σ ^ 2) := by sorry
