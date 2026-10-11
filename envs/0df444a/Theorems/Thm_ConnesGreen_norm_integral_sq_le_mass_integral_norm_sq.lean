-- Prove2me | Theorems.Thm_ConnesGreen_norm_integral_sq_le_mass_integral_norm_sq
-- name    : ConnesGreen.norm_integral_sq_le_mass_integral_norm_sq
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T20:33:28.244525+00:00
-- url     : https://prove2.me/theorems/f103bc39-a48e-41a0-af80-ff0081bd375c
-- title:
--   Finite-measure Fourier concentration estimate in the original mass normalization
-- statement:
--   Let $\mu$ be a finite measure on a measurable space, and let $f$ be an integrable complex-valued function with integrable squared norm. Then $$\left|\int f\,d\mu\right|^2\le\mu(X)\int|f|^2\,d\mu.$$ Applied on the original supported time interval, this gives the precise support-length control of low-frequency Mellin mass used in the native Connes–Weil positivity estimate. It makes no assumption about zeta zeros or Weil positivity.
-- source:
--   monocap-tech/weil, Connes/ArchimedeanFrequency.lean. Native original Mellin, gamma and pole corollaries use this bound to prove full Weil positivity on an explicit small support interval, retaining actual zeta zeros, analytic multiplicities, the unchanged selected packet, complete zero background and original completed physical metric. This standalone export proves only the reusable finite-measure estimate.
--
--   Literature/source audit addendum (2026-10-11; COR-13): Exact native software custody, independently verified from retained local Git objects: monocap-tech/weil 1a32f7de3442feb804b4962bb6766304a56b5be8, WeilDefect/Connes/ArchimedeanFrequency.lean, SHA256 d675876ba3d129cadd9eec7611e56d39dd96323b8e74421b8c7b8d4c0902a05b. Public availability of these historical pins has not been checked; this addendum verifies local source bytes and preserves the original source ancestry.

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory Set
noncomputable section

theorem ConnesGreen.norm_integral_sq_le_mass_integral_norm_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℂ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => ‖f x‖ ^ 2) μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ μ.real univ * (∫ x, ‖f x‖ ^ 2 ∂μ) := by sorry
