-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen14_singular_levy_first_moment_integrable
-- name    : AvramDividend.Classical.avram_gen14_singular_levy_first_moment_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:54:21.637705+00:00
-- url     : https://prove2.me/theorems/a6ebe28d-fcd2-4ffe-a27d-cf81983cf609
-- title:
--   Integrability of the absolute first moment under the singular negative Levy measure
-- statement:
--   The magnitude of the jump mark is Bochner integrable against the proposed singular spectrally negative Levy measure. This establishes the bounded first-moment property used when constructing the finite-variation stochastic process, and its proof uses the exact previously computed nonzero moment.
-- source:
--   Previously proved exact first-moment value two; pinned integral_undef implies a non-integrable real Bochner integrand has zero integral.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gen14_singular_levy_first_moment_integrable :
    Integrable (fun z : ℝ => |z|)
      (volume.withDensity (fun z : ℝ =>
        if z ∈ Ioo (-1 : ℝ) 0
        then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)) := by sorry
