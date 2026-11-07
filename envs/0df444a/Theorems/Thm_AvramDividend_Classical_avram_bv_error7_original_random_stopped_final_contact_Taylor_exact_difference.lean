-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_random_stopped_final_contact_Taylor_exact_difference
-- name    : AvramDividend.Classical.avram_bv_error7_original_random_stopped_final_contact_Taylor_exact_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:28:18.173195+00:00
-- url     : https://prove2.me/theorems/c959f9bd-53c1-40d5-8ba2-c7b300b2dfb5
-- title:
--   Exact original random-stopped final contact Taylor cell equals full minus strict physical sources
-- statement:
--   For the original Lévy process X and actual dividend strategy D, the full stopped physical-grid discounted Taylor sum minus the strict precontact sum is exactly the unique final contact-cell remainder when k>0, with zero contribution when the stopping index is zero.
-- source:
--   Use Finset.sum_range_succ with k-1+1=k in the nonzero-clock case and the empty sum identity in the zero-clock case. The summand is explicitly constructed from the original X, original right-limit D, raw negative jump source J, Y=X+J and discounted C1 Taylor expression. This is the exact pathwise splitting needed for contact L1 absorption; no BV prebudget is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_random_stopped_final_contact_Taylor_exact_difference
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (ErrFull ErrStrict : ℕ → Ω → ℝ)
    (hFull : ∀ m ω, ErrFull m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
       let g : ℕ → ℝ := fun i =>
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)
       ∑ i ∈ Finset.range (k m ω), g i))
    (hStrict : ∀ m ω, ErrStrict m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
       let g : ℕ → ℝ := fun i =>
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)
       ∑ i ∈ Finset.range (k m ω - 1), g i)) :
    ∀ m ω, ErrFull m ω - ErrStrict m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
       let g : ℕ → ℝ := fun i =>
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)
       if k m ω = 0 then 0 else g (k m ω - 1)) := by sorry
