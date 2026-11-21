-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a29_original_finitecap_actual_gaussian_crossing_expected_L1_automatic_envelope
-- name    : AvramDividend.Classical.avram_a29_original_finitecap_actual_gaussian_crossing_expected_L1_automatic_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:19:46.454433+00:00
-- url     : https://prove2.me/theorems/f0252691-73fd-4e67-b1df-c2fb13a27c71
-- title:
--   Actual finitecap original Gaussian compact-band random crossing spatial expected positive error vanishes with automatic L1 envelope
-- statement:
--   At true original random stopped Gaussian mesh clocks and bounded positive reserve band [a,b]≤finite dividend cap c, the caplinear spatial correction positive-part expectation vanishes as mesh shrinks. No externally assumed envelope: build common integrable Gaussian increment majorant from proved original horizon-square supremum a28 plus proved caplinear global scalar difference bound a25. Apply original Gaussian random-crossing pathwise and dominated-convergence sources a27. The value is original w on admissible reserves and caplinear above c, preserving original X, discount and finitecap overshoots. The other Ito, dividend and ruin terms remain separate.
-- source:
--   Original stopped zerojump physical Gaussian finitecap caplinear positive-crossing L1 source with built rather than assumed majorant.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a29_original_finitecap_actual_gaussian_crossing_expected_L1_automatic_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Set.Icc 0 T ∧ t m ω ∈ Set.Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1))
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (a b r : ℝ) (hr : 0 < r) (hra : r ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c)
    (y : ℕ → Ω → ℝ)
    (hy : ∀ᵐ ω ∂P, ∀ m, y m ω ∈ Set.Icc a b)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       w (y m ω)) 0) P) :
    Tendsto (fun m => ∫ ω,
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       w (y m ω)) 0 ∂P)
       atTop (nhds (0 : ℝ)) := by sorry
