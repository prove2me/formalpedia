-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_quadratic_martingale_increment_condExp_zero
-- name    : AvramDividend.Classical.avram_lsv_quadratic_martingale_increment_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T11:59:23.868564+00:00
-- url     : https://prove2.me/theorems/e86f9f08-4ae8-44bd-8969-1b32646951e2
-- title:
--   Quadratic-compensator martingales give conditional zero centred square increments
-- statement:
--   General quadratic martingale source lemma: if M and M squared minus A are true martingales and M is square integrable, the conditional expectation at s of (M_t-M_s)^2-(A_t-A_s) is zero. Adapted from dufeteller/lean-lsv MartingaleQuadraticIncrement.lean, CC BY 4.0. The result can be instantiated to the original Gaussian compensator after proving its real martingale representation, without assuming one exists.

import Mathlib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
set_option autoImplicit false
noncomputable section

/-
Adapted from dufeteller/lean-lsv, LSV/MartingaleQuadraticIncrement.lean,
martingale_quadratic_increment_condExp_zero and martingale_increment_condExp_zero,
commit a5f604de2e1ae431de4cbecde23e5694a12ba719.
Original authors credited in source repository; CC BY 4.0.
Adaptation inlines the martingale increment identity to avoid importing LSV.
-/

theorem AvramDividend.Classical.avram_lsv_quadratic_martingale_increment_condExp_zero
    {Ω ι : Type*} [MeasurableSpace Ω] [Preorder ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ι (inferInstance : MeasurableSpace Ω))
    (M A : ι → Ω → ℝ) (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t z => (M t z)^2 - A t z) ℱ μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (s t : ι) (hst : s ≤ t) :
    condExp (ℱ s) μ (fun z => (M t z - M s z)^2 - (A t z - A s z))
      =ᵐ[μ] (fun _ => (0 : ℝ)) := by sorry
