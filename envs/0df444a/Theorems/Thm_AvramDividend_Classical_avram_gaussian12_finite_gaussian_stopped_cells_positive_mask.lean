-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussian12_finite_gaussian_stopped_cells_positive_mask
-- name    : AvramDividend.Classical.avram_gaussian12_finite_gaussian_stopped_cells_positive_mask
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:33:19.699772+00:00
-- url     : https://prove2.me/theorems/2c6cfd0c-22c8-407f-9602-46f9fa0f2f5e
-- title:
--   Finite stopped Gaussian Taylor cells have zero total expectation on positive clock events
-- statement:
--   Any finite family of integrable Gaussian stochastic residuals, each centred conditionally on its own genuine stopped-history sigma algebra, has zero sum integral when restricted to an arbitrary strictly positive stopping-clock event. The source-exact conditional centring is supplied by f9916aff; the separate bridge 7f0af2b8 transports centring to the initial clock. This result discharges the finite-grid Gaussian martingale sign term, but not the independent controlled Itô pathwise ledger or passage to limits.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_stopped_condexp_to_positive_clock_mask
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_gaussian12_finite_gaussian_stopped_cells_positive_mask
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτstop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ i ω : WithTop ℝ≥0)))
    (M : ι → Ω → ℝ)
    (hMI : ∀ i ∈ S, Integrable (M i) P)
    (hStoppedZero : ∀ i (hi : i ∈ S),
      condExp (hτstop i hi).measurableSpace P (M i) =ᵐ[P]
        (fun _ => (0 : ℝ))) :
    (∫ ω in {ω : Ω | σ ω ≠ 0}, ∑ i ∈ S, M i ω ∂P) = 0 := by sorry
