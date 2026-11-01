-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightEndpoint_stieltjes_simpleGrid_lintegral
-- name    : AvramDividend.Classical.avram_wave4_03_rightEndpoint_stieltjes_simpleGrid_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:19:50.594344+00:00
-- url     : https://prove2.me/theorems/009602cf-2d1b-48e1-ad54-a51329b2a5b9
-- title:
--   Exact right-endpoint simple-grid Stieltjes integral of every monotone control
-- statement:
--   The sum of right-endpoint step functions over any finite family of half-open (u_i,u_{i+1}] intervals has exact nonnegative Stieltjes integral equal to the sum of right-endpoint coefficients times monotone right-limit Stieltjes masses. No purely atomic assumption; valid for diffuse, singular-continuous, and right-atomic measures, including zero or overlapping intervals.
-- source:
--   Pinned Mathlib StieltjesFunction.measure_Ioc, lintegral_finset_sum, lintegral_indicator_const

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_rightEndpoint_stieltjes_simpleGrid_lintegral
    (g : ℝ → ℝ) (hg : Monotone g)
    (u : ℕ → ℝ) (n : ℕ) (c : ℕ → ℝ≥0∞) :
    (∫⁻ t : ℝ, ∑ i ∈ Finset.range n,
      (Ioc (u i) (u (i + 1))).indicator
        (fun _ : ℝ => c (i + 1)) t
      ∂hg.stieltjesFunction.measure) =
    ∑ i ∈ Finset.range n,
      c (i + 1) *
        ENNReal.ofReal
          (hg.stieltjesFunction (u (i + 1)) -
            hg.stieltjesFunction (u i)) := by sorry
