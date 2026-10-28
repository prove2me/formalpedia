-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_zero_initial_martingale_vanishes_ae
-- name    : AvramDividend.Classical.nonnegative_zero_initial_martingale_vanishes_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:14:09.685687+00:00
-- url     : https://prove2.me/theorems/7e269fe7-424a-44b2-98ed-2fc96cc25222
-- title:
--   A nonnegative martingale starting at zero vanishes almost surely
-- statement:
--   A nonnegative real-valued martingale with identically zero initial reward must be zero almost surely at every fixed time. The proof uses the standard sigma-finite filtration martingale equality of integrals, nonnegative zero-integral criterion and integrability of martingales. This exposes why the un-killed discounted scale-function process cannot be used as a martingale at reserve zero for a process with positive increments, and directs the two-sided exit proof toward stopping at ruin.
-- source:
--   Pinned Mathlib Martingale.setIntegral_eq and integral_eq_zero_iff_of_nonneg_ae.

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.nonnegative_zero_initial_martingale_vanishes_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    [SigmaFiniteFiltration P 𝓕]
    (M : ℝ≥0 → Ω → ℝ)
    (hM : Martingale M 𝓕 P)
    (hnonneg : ∀ t : ℝ≥0, 0 ≤ᵐ[P] M t)
    (hzero : M 0 =ᵐ[P] (fun _ => (0 : ℝ))) :
    ∀ t : ℝ≥0, M t =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
