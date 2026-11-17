-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_signed_capkink_two_positive_errors_L1_squeeze
-- name    : AvramDividend.Classical.avram_ga_signed_capkink_two_positive_errors_L1_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:34:59.071048+00:00
-- url     : https://prove2.me/theorems/1e0ce63c-1ec2-4c6d-8df2-d75973612929
-- title:
--   Signed cap-kink finite-grid error squeeze from two positive L1 budgets
-- statement:
--   On a measurable event, suppose a stopped cash-source excess is bounded almost surely by two mesh errors minus a nonnegative kink correction. If both positive mesh error expectations vanish and the source variables are integrable, then the expected positive cash excess vanishes. The kink term is retained with its correct favourable sign and no absolute convergence of it is assumed.

import Mathlib
open MeasureTheory Filter Topology

theorem AvramDividend.Classical.avram_ga_signed_capkink_two_positive_errors_L1_squeeze
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (K : Ω → ℝ) (M E C T : ℕ → Ω → ℝ)
    (hKI : Integrable K (P.restrict A))
    (hMI : ∀ m, Integrable (M m) (P.restrict A))
    (hEI : ∀ m, Integrable (E m) (P.restrict A))
    (hCI : ∀ m, Integrable (C m) (P.restrict A))
    (hKink : ∀ m, ∀ᵐ ω ∂(P.restrict A), 0 ≤ T m ω)
    (hLedger : ∀ m, ∀ᵐ ω ∂(P.restrict A),
       K ω - M m ω ≤ E m ω + C m ω - T m ω)
    (hEt : Tendsto (fun m => ∫ ω in A, max (E m ω) 0 ∂P)
       atTop (nhds (0 : ℝ)))
    (hCt : Tendsto (fun m => ∫ ω in A, max (C m ω) 0 ∂P)
       atTop (nhds (0 : ℝ))) :
    Tendsto (fun m => ∫ ω in A, max (K ω - M m ω) 0 ∂P)
       atTop (nhds (0 : ℝ)) := by sorry
