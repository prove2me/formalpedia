-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ftap_zerojump_original_stopped_continuous_ae
-- name    : AvramDividend.Classical.avram_ftap_zerojump_original_stopped_continuous_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:40:09.293359+00:00
-- url     : https://prove2.me/theorems/a29228c5-21f3-4094-92cc-c2313c6e2ec5
-- title:
--   Original zero-Levy-jump Gaussian stopped surplus driver has almost-sure continuous paths
-- statement:
--   For the original spectrally-negative Lévy driver with zero jump measure, any path stopped at a (possibly infinite) clock remains continuous almost surely. Adapt the by-cases finite-or-top stopped-path proof of FTAPTheorem42/Stochastic/Martingale/Basic/RightContinuousStoppedMartingale.lean using the already Proved Avram zero-jump Gaussian continuous-path result avram_gbB199_original_zerojump_gaussian_FV_semimartingale_preflight. The statement uses the original X.X path and the same stochastic clock, adding no artificial stochastic source witnesses.
-- source:
--   https://github.com/selpoG/lean-ftap-closedness/blob/8c9c46e1b6e455f7d3069062957d4363879836ce/FTAPTheorem42/Stochastic/Martingale/Basic/RightContinuousStoppedMartingale.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB199_original_zerojump_gaussian_FV_semimartingale_preflight
open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_ftap_zerojump_original_stopped_continuous_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → WithTop ℝ≥0) :
    ∀ᵐ ω ∂P, Continuous
      (fun t : ℝ≥0 => MeasureTheory.stoppedProcess X.X τ t ω) := by sorry
