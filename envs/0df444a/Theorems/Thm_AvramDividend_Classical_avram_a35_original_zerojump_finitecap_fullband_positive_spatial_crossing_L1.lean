-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a35_original_zerojump_finitecap_fullband_positive_spatial_crossing_L1
-- name    : AvramDividend.Classical.avram_a35_original_zerojump_finitecap_fullband_positive_spatial_crossing_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:08:00.885797+00:00
-- url     : https://prove2.me/theorems/f2c7f70c-12f3-4def-a1e2-6532e88ed42b
-- title:
--   Original actual finite-cap Gaussian positive crossing vanishes over full [0,C] including ruin contact
-- statement:
--   For the original ν=0 spectrally negative Lévy X, true random clock increments at mesh distance ≤T/(m+1), and any actual pre-ruin postpayment reserve y_m∈[0,c], show expected positive caplinear spatial crossing residual tends to zero. Crucially includes the zero-reserve boundary, unlike the already proved positive-interior crossing theorem a33. Uses original true random increment convergence f76b4c7d, original common integrable Gaussian increment envelope 93b870f2, caplinear crossing difference bound 4d5d7a6f, one-sided zero-contact scalar lemma a34 and dominated-convergence lemma a108. The statement requires only physical residual measurability. It does not assume the expected HJB cash bound or substitute artificial noise.
-- source:
--   Original full physical finitecap positive Gaussian crossing source, beyond strict positive localisations; with zero-reserve ruin contact and true stochastic time-grid increments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a35_original_zerojump_finitecap_fullband_positive_spatial_crossing_L1
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
         w (y m ω)) 0) P) :
    Tendsto (fun m => ∫ ω,
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
         then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
         else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
         w (y m ω)) 0 ∂P) atTop (nhds (0 : ℝ)) := by sorry
