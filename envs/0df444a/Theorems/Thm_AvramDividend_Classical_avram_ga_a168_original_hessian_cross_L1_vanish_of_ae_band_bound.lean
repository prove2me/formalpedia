-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a168_original_hessian_cross_L1_vanish_of_ae_band_bound
-- name    : AvramDividend.Classical.avram_ga_a168_original_hessian_cross_L1_vanish_of_ae_band_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:38:49.036087+00:00
-- url     : https://prove2.me/theorems/927131fd-9061-4386-a755-dcfd1dea160e
-- title:
--   Original physical-grid Hessian cross source L1 vanishing under almost-sure compact-band coefficient bounds
-- statement:
--   A finite stopped-grid weighted Gaussian quadratic drift-cross sum vanishes in expected absolute L1 if its unweighted source cross energy vanishes in L1 and the Hessian coefficient is uniformly bounded almost everywhere on the source band. This removes the overly strong global-in-outcomes bound required by the earlier proved a89 and matches the genuine source compact prefix hypotheses needed by a150.
-- source:
--   General a.e. weighted integral dominance, analogous to Proved ga_a89 but with almost-sure compact original prefix bounds.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a168_original_hessian_cross_L1_vanish_of_ae_band_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℕ → Finset ℕ) (H R : ℕ → ℕ → Ω → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ m, ∀ᵐ ω ∂P, ∀ i ∈ S m, |H m i ω| ≤ K)
    (hCrossI : ∀ m, Integrable (fun ω =>
      |∑ i ∈ S m, H m i ω / 2 * R m i ω|) P)
    (hEnergyI : ∀ m, Integrable (fun ω =>
      ∑ i ∈ S m, |R m i ω|) P)
    (hEnergyL1 : Tendsto (fun m =>
      ∫ ω, (∑ i ∈ S m, |R m i ω|) ∂P) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m =>
      ∫ ω, |∑ i ∈ S m, H m i ω / 2 * R m i ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
