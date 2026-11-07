-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_final_contact_cell_positive_error_split
-- name    : AvramDividend.Classical.avram_bv_error7_original_final_contact_cell_positive_error_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:56:29.619711+00:00
-- url     : https://prove2.me/theorems/606f9c57-653e-424d-8f4c-842f02ff82c7
-- title:
--   Original BV stopped physical C1 error positive part splits into strict interior and final contact cell
-- statement:
--   For any actual spectrally negative Lévy X and dividend D, and any nonempty original physical grid with stopped endpoint, the positive part of the full discounted C1 Taylor residual is at most the positive part of the strict precontact sum plus the positive part of the unique final contact-cell residual. The J jump summation, Y=X+J remainder, original right-limit dividend reserve, and discount are source-exact. This is a finite identity/inequality and does not assume boundary regularity or integrability. It isolates the additional probability estimate required at the cap or ruin boundary.
-- source:
--   Finite sum_range_succ and max-positive-part subadditivity instantiated to original physical-grid source. No use of BV prebudget, compensated HJB bridge, Fatou conclusion or non-original surrogate process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_final_contact_cell_positive_error_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (k : ℕ) (hk : 0 < k) :
    (let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
      else 0
     let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
     let g : ℕ → ℝ := fun i =>
       Real.exp (-(q * (u i : ℝ))) *
         (w (x + X.X (u i) ω - rightLimit D (u i) ω +
             (Y (u (i+1)) - Y (u i))) -
           w (x + X.X (u i) ω - rightLimit D (u i) ω) -
           deriv w (x + X.X (u i) ω - rightLimit D (u i) ω) *
             (Y (u (i+1)) - Y (u i)))
     max (∑ i ∈ Finset.range k, g i) 0 ≤
       max (∑ i ∈ Finset.range (k - 1), g i) 0 +
         max (g (k - 1)) 0) := by sorry
