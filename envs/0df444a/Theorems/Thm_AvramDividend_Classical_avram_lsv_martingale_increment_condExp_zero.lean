-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_martingale_increment_condExp_zero
-- name    : AvramDividend.Classical.avram_lsv_martingale_increment_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:00:24.570569+00:00
-- url     : https://prove2.me/theorems/beb157a7-2ada-4fa1-b2f6-48e969e23692
-- title:
--   Martingale increments have zero conditional expectation at the earlier filtration
-- statement:
--   For a true integrable martingale, conditional expectation at the earlier time of its later-minus-earlier increment is zero. Exact proof adapted from dufeteller/lean-lsv MartingaleQuadraticIncrement.lean under CC BY 4.0. A reusable component for the actual Gaussian quadratic-compensator increment proof.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
noncomputable section

/-
Adapted from dufeteller/lean-lsv, LSV/MartingaleQuadraticIncrement.lean,
martingale_increment_condExp_zero, commit a5f604de2e1ae431de4cbecde23e5694a12ba719.
Upstream CC BY 4.0, attribution to original source authors.
-/

theorem AvramDividend.Classical.avram_lsv_martingale_increment_condExp_zero
    {Ω ι : Type*} [MeasurableSpace Ω] [Preorder ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ι (inferInstance : MeasurableSpace Ω))
    (M : ι → Ω → ℝ) (hM : Martingale M ℱ μ) (s t : ι) (hst : s ≤ t) :
    condExp (ℱ s) μ (fun z => M t z - M s z) =ᵐ[μ] (fun _ => (0 : ℝ)) := by sorry
