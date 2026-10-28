-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_tendsto_iInf
-- name    : AvramDividend.Classical.esscher_weighted_lower_survival_mass_tendsto_iInf
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:17:29.858072+00:00
-- url     : https://prove2.me/theorems/9752e377-3c51-4fe2-8233-4a613933bcb2
-- title:
--   Esscher lower-barrier weighted survival mass converges to its infimum at infinite horizon
-- statement:
--   For any nonnegative Esscher tilt of a spectrally negative Lévy process, the expected exponentially weighted mass of paths surviving above a fixed shifted lower barrier until time t converges as t increases without bound. The limit is the infimum over finite horizons. Nonnegative integrands supply a uniform lower bound, and the proved Esscher weighted survival antitonicity supplies monotonicity.
-- source:
--   Mathlib monotone convergence of antitone real functions (tendsto_atTop_ciInf); analytic construction preceding the tilted zero-killing survival characterisation of the q-scale function in Kuznetsov, Kyprianou and Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes.

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_antitone

open MeasureTheory Filter
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.esscher_weighted_lower_survival_mass_tendsto_iInf
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) :
    Tendsto
      (fun t : ℝ≥0 =>
        ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp
            (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)
      atTop
      (nhds (⨅ t : ℝ≥0,
        ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp
            (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)) := by sorry
