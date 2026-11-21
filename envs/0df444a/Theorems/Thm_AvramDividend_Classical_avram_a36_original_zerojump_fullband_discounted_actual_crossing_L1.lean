-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a36_original_zerojump_fullband_discounted_actual_crossing_L1
-- name    : AvramDividend.Classical.avram_a36_original_zerojump_fullband_discounted_actual_crossing_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:15:23.991188+00:00
-- url     : https://prove2.me/theorems/699a846f-63b1-4935-a0f6-c7649136be58
-- title:
--   Actual finitecap stopped Gaussian full-reserve-band discounted positive crossing error tends to zero
-- statement:
--   Apply the Proved original full-band unweighted positive Gaussian crossing L1 theorem a35 and uniform integrable majorant a34b to the true original X random-clock spatial crossing, including zero reserve, then transfer vanishing expected error through actual predictable discount exp(-qρ_m) in [0,1] using Proved a30 discount-weighted nonnegative L1 squeeze. This is the exact original positive crossing error with discount at stopping time, without strict-positive reserve localisation and without assuming the expected HJB cash budget.
-- source:
--   Original zerojump finitecap true stopped Gaussian crossing spatial positive discounted expected L1 source, including ruin contact.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a36_original_zerojump_fullband_discounted_actual_crossing_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Set.Icc 0 T ∧ t m ω ∈ Set.Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1))
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw0 : 0 ≤ w 0) (hwneg : ∀ z : ℝ, z < 0 → w z = 0)
    (hwcont : ContinuousOn w (Set.Ici 0))
    (y : ℕ → Ω → ℝ)
    (hy : ∀ᵐ ω ∂P, ∀ m, y m ω ∈ Set.Icc 0 c)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
         then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
         else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
         w (y m ω)) 0) P)
    (q : ℝ) (hq : 0 ≤ q)
    (ρ : ℕ → Ω → ℝ≥0) (hρmeas : ∀ m, Measurable (ρ m)) :
    Tendsto (fun m => ∫ ω,
      Real.exp (-(q * (ρ m ω : ℝ))) * max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
         then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
         else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
         w (y m ω)) 0 ∂P) atTop (nhds (0 : ℝ)) := by sorry
