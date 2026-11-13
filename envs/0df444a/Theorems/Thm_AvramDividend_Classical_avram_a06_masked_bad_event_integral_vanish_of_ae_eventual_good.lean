-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_masked_bad_event_integral_vanish_of_ae_eventual_good
-- name    : AvramDividend.Classical.avram_a06_masked_bad_event_integral_vanish_of_ae_eventual_good
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T11:27:40.964227+00:00
-- url     : https://prove2.me/theorems/354dbd7e-2371-4d97-ab6a-0728f4e1d285
-- title:
--   A06 original-grid exceptional-event integrable envelope has vanishing mean
-- statement:
--   For the physical-grid and compact-band localisation used in A06, every measurable bad event that eventually disappears almost everywhere contributes asymptotically zero expected error when its pathwise magnitude is controlled by a fixed integrable original-source envelope. This provides the rigorous exceptional-set tail estimate, avoiding L1 assumptions on the signed HJB generator residual. The genuine original source envelope and eventual interior-band coverage must be verified separately.

import Mathlib
open MeasureTheory Filter Set
open scoped Topology Classical
noncomputable section

theorem AvramDividend.Classical.avram_a06_masked_bad_event_integral_vanish_of_ae_eventual_good
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H : Ω → ℝ) (hHm : Measurable H) (hHI : Integrable H P)
    (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hEventually : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) :
    Tendsto (fun n : ℕ => ∫ ω, (if ω ∈ s n then (0 : ℝ) else H ω) ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
