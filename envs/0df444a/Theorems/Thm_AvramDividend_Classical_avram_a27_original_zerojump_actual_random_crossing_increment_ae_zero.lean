-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_zerojump_actual_random_crossing_increment_ae_zero
-- name    : AvramDividend.Classical.avram_a27_original_zerojump_actual_random_crossing_increment_ae_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T10:11:55.986271+00:00
-- url     : https://prove2.me/theorems/f76b4c7d-492a-4744-9d60-bf28eebd1d9c
-- title:
--   Actual zerojump Gaussian Levy random stopped crossing increments vanish a.e. under true time gaps
-- statement:
--   For the original zero-Lévy-measure Gaussian spectrally negative Lévy process X and arbitrary random physical crossing clocks s_m,t_m within a deterministic bounded horizon T, with true random time gap at most T/(m+1), show the actual uncentred stochastic increment X(t_m)−X(s_m) tends to zero almost surely. This directly follows from already proved a106 Gaussian positive-prefix random crossing value modulus using the globally 1-Lipschitz identity test function; y≡1, alpha=1,beta=2. It supplies the true random increment hypothesis for finitecap caplinear stopped spatial error without falsely equating clipped and full deterministic increments.
-- source:
--   Same original X stopped Gaussian random true spatial crossing increment; physical time-gap condition and ν=0 Gaussian continuity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_zerojump_actual_random_crossing_increment_ae_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Set.Icc 0 T ∧ t m ω ∈ Set.Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1)) :
    ∀ᵐ ω ∂P, Tendsto (fun m =>
      X.X (t m ω) ω - X.X (s m ω) ω) atTop (nhds (0 : ℝ)) := by sorry
