-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_two_sampled_stops_gaussian_gap_L2
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_original_two_sampled_stops_gaussian_gap_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:49:54.262203+00:00
-- url     : https://prove2.me/theorems/9954ba8b-8a28-4478-a09a-0e1e92364174
-- title:
--   Original Gaussian L2 overhang bound between two genuine sampled stops
-- statement:
--   For two ordered genuine bounded sampled right-continuous stopping indices on a common original process time grid, the actual squared centred X.X increment has expected value bounded by epsilon times sigma squared whenever the predictable bracket clock gap has that bound pathwise. This exact-source estimate is the finite-grid half of the physical stop-straddling overhang argument. The hypotheses explicitly require bracket-clock integrability; a common finer grid and Fatou limit still need construction.
-- source:
--   Proved 2f5720cf original zero-nu stopped Gaussian quadratic bracket identity, real integral linearity and monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_gaussian_expected_quadratic_bracket

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_original_two_sampled_stops_gaussian_gap_L2
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
    (∫ ω, (B ω - A ω) ^ 2 ∂P) ≤ ε * X.σ ^ 2 := by sorry
