-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_two_scale_budget_forces_B_L1
-- name    : AvramDividend.Classical.avram_bvb_two_scale_budget_forces_B_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T11:19:41.973728+00:00
-- url     : https://prove2.me/theorems/68799a9f-69e5-4449-88bf-ba966c3bbb27
-- title:
--   Two-scale stopped nonnegative cash budget and nonpositive B imply integrability of the original B grid
-- statement:
--   A probability-space pathwise cash upper bound F≤a+M+B+positive error channels, with nonnegative cash, centred integrable martingale M, integrable positive errors, and nonpositive measurable physical drift grid B forces B to be L1 integrable. This exposes integrability as a necessary consequence of any claimed original two-scale BV budget, relevant to the BV B no-extra-B-L1 theorem.
-- source:
--   Under B≤0 and F≥0, its absolute value −B is pointwise bounded by |a|+|M|+the two positive error channels. The envelope is integrable and B is a.e. measurable, so the pinned Integrable.mono prime theorem applies.

import Mathlib
open Classical MeasureTheory Filter
open scoped Topology

theorem AvramDividend.Classical.avram_bvb_two_scale_budget_forces_B_L1
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (a : ℝ) (F B M E₁ E₂ : Ω → ℝ)
    (hF : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hB : ∀ᵐ ω ∂P, B ω ≤ 0)
    (hBmeas : AEStronglyMeasurable B P)
    (hM : Integrable M P)
    (hE₁ : Integrable (fun ω => max (E₁ ω) 0) P)
    (hE₂ : Integrable (fun ω => max (E₂ ω) 0) P)
    (hBudget : ∀ᵐ ω ∂P,
      F ω ≤ a + M ω + B ω +
        max (E₁ ω) 0 + max (E₂ ω) 0) :
    Integrable B P := by sorry
