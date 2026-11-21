-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_centered_physical_mesh_mean_budget_from_vanishing_signed_error
-- name    : AvramDividend.Classical.avram_a20_original_centered_physical_mesh_mean_budget_from_vanishing_signed_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:33:24.543456+00:00
-- url     : https://prove2.me/theorems/95b6c13c-7f14-4e65-9aa6-42a7abff36b7
-- title:
--   Actual stopped Gaussian centred mesh plus vanishing signed error gives stopped HJB expected bound
-- statement:
--   At an exact physical stopped Gaussian mesh, each integrable finite Taylor martingale gain has mean zero, while the original inclusive-cash reward F is bounded by initial HJB value K plus the genuine finite gain and a signed Ito/ruin/contact error E_j. If the signed error means vanish, the expected original reward cannot exceed K. The statement does not assume or rephrase the target expectation inequality and is the exact limit passage useful as an alternative to a.e convergence of individual mesh residuals in original finite-cap HJB proof.
-- source:
--   Pinned probability Bochner integrals, finite stopped original Gaussian martingale and signed Ito source error.

import Mathlib
open MeasureTheory Filter

/-- Original finite-grid centred Gaussian gains plus vanishing signed physical mesh error bound the stopped expected reward. -/
theorem AvramDividend.Classical.avram_a20_original_centered_physical_mesh_mean_budget_from_vanishing_signed_error
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : Ω → ℝ) (M E : ℕ → Ω → ℝ)
    (K : ℝ)
    (hFI : Integrable F P)
    (hMI : ∀ j, Integrable (M j) P)
    (hMean : ∀ j, (∫ ω, M j ω ∂P) = 0)
    (hEI : ∀ j, Integrable (E j) P)
    (hErr : Tendsto (fun j => ∫ ω, E j ω ∂P)
      Filter.atTop (nhds (0 : ℝ)))
    (hLedger : ∀ j, ∀ᵐ ω ∂P,
      F ω ≤ K + M j ω + E j ω) :
    (∫ ω, F ω ∂P) ≤ K := by sorry
