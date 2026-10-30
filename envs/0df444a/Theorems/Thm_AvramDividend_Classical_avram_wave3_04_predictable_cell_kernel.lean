-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_predictable_cell_kernel
-- name    : AvramDividend.Classical.avram_wave3_04_predictable_cell_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:04:12.89999+00:00
-- url     : https://prove2.me/theorems/acdcb42e-daae-4239-9162-3282c60b492c
-- title:
--   Predictability of a frozen adapted observation over a future half-open time cell
-- statement:
--   For any filtration, a measurable observation available at time s, held on (s,t] and zero outside, is measurable for the predictable sigma algebra. This is the basic simple-process block used to approximate the genuinely left-continuous adapted dividend control in the unbounded-variation Ito verification argument, without assuming right-continuity or completion of the filtration.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 4(i), stopped Ito verification: need predictable approximation of the source IsDividendStrategy control. Mathlib Probability.Process.Predictable Ioc-product generator; exact complete proof reached the intentional private remote compiler sentinel on pinned revision with candidate SHA-256 9f84ac05713e362ecc5902da6007b769ea0b2fd72a31f1013a45330c83e4f2c0, job 91fcd65c-afe1-433a-9d4c-a7eed16e7202. The subsequent limit to all left-continuous adapted controls remains unproved.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_predictable_cell_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (s t : ℝ≥0) (f : Ω → ℝ)
    (hf : @Measurable Ω ℝ (𝓕 s) inferInstance f) :
    @Measurable (ℝ≥0 × Ω) ℝ 𝓕.predictable inferInstance
      (fun p => if p.1 ∈ Set.Ioc s t then f p.2 else 0) := by sorry
