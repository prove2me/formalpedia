-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin29_finite_product_bounded_kernel_integrable
-- name    : AvramDividend.Classical.avram_mix_fin29_finite_product_bounded_kernel_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T17:32:18.849451+00:00
-- url     : https://prove2.me/theorems/b811413f-2d71-4009-80e8-ed6286b1b6ff
-- title:
--   Uniformly bounded predictable mark kernels are L1 on finite time-mark product compensators
-- statement:
--   An original predictable finite-time reference measure and a finite negative-mark intensity yield a finite product compensator. Any a.e.-strongly-measurable real kernel uniformly bounded by nonnegative K is therefore integrable against that product compensator. This is the exact missing Integrable G N entry hypothesis for Proved original stopped compensated source martingale f445799e, after the finite-mixed compact reserve kernel bound 86bc48a7 is applied. It requires no absolute first moment of negative jumps.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin29_finite_product_bounded_kernel_integrable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (hμ : μ Set.univ < ∞) (hν : ν Set.univ < ∞)
    (H : α × β → ℝ)
    (hHm : AEStronglyMeasurable H (μ.prod ν))
    (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ p, |H p| ≤ K) :
    Integrable H (μ.prod ν) := by sorry
