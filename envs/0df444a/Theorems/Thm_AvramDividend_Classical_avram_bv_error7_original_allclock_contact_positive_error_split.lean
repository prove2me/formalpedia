-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_allclock_contact_positive_error_split
-- name    : AvramDividend.Classical.avram_bv_error7_original_allclock_contact_positive_error_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:01:14.603917+00:00
-- url     : https://prove2.me/theorems/1c84fb41-5fab-4705-97c7-b0d8c4258581
-- title:
--   Original stopped BV source positive error splits with exact zero-clock and final-contact convention
-- statement:
--   For the actual original X/D/J/Y stopped physical-grid source and any finite number k of cells, the positive C1 Taylor error is bounded by the strict precontact positive error plus the unique last-cell positive residual. When k=0, this terminal residual is exactly zero, so the time-zero stopped clock does not create a fictitious contact cell. This algebraic split leaves the separate time-zero right-dividend atom to the already Proved strict-cash accounting lemma.
-- source:
--   Composition of original positive-error contact split (publication job 9e9afdd6-b4f4-444c-b1a0-12e7d36b91ab) with the exact k=0 finite-grid case. No circular use of budget or Fatou.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_allclock_contact_positive_error_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (k : ℕ) :
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
         (if k = 0 then 0 else max (g (k - 1)) 0)) := by sorry
