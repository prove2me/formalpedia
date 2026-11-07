-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_full_stopped_Taylor_positive_error_L1_of_exact_split
-- name    : AvramDividend.Classical.avram_bv_error7_original_full_stopped_Taylor_positive_error_L1_of_exact_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:45:33.169907+00:00
-- url     : https://prove2.me/theorems/e857d083-2f2c-4647-95d4-e81ffd0d9e1a
-- title:
--   Original stopped full Taylor positive-error L1 via exact contact split
-- statement:
--   For the genuine original X,D stopped physical grid, if the strict and final-contact Taylor positive parts are integrable with vanishing expected values, then the complete physical-grid Taylor positive part is integrable and its expectation tends to zero. The authentic contact identity is derived, not assumed.
-- source:
--   Imports accepted original finite-grid full/strict contact exact difference plus strict/contact positive-error L1 absorption; no BV prebudget, no invented process, and no assumption of an arbitrary full-minus-strict identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_full_stopped_Taylor_positive_error_L1_of_exact_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (ErrFull ErrStrict ErrContact : ℕ → Ω → ℝ)
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
       ∑ i ∈ Finset.range (k m ω - 1), g i))
    (hContact : ∀ m ω, ErrContact m ω =
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
       if k m ω = 0 then 0 else g (k m ω - 1)))
    (hFullMeas : ∀ m, AEStronglyMeasurable (fun ω => max (ErrFull m ω) 0) P)
    (hStrictInt : ∀ m, Integrable (fun ω => max (ErrStrict m ω) 0) P)
    (hContactInt : ∀ m, Integrable (fun ω => max (ErrContact m ω) 0) P)
    (hStrictMean : Tendsto (fun m => ∫ ω, max (ErrStrict m ω) 0 ∂P) atTop (nhds (0 : ℝ)))
    (hContactMean : Tendsto (fun m => ∫ ω, max (ErrContact m ω) 0 ∂P) atTop (nhds (0 : ℝ))) :
    (∀ m, Integrable (fun ω => max (ErrFull m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (ErrFull m ω) 0 ∂P) atTop (nhds (0 : ℝ)) := by sorry
