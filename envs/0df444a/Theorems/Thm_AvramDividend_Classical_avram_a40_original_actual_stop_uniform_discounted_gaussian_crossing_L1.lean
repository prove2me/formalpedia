-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a40_original_actual_stop_uniform_discounted_gaussian_crossing_L1
-- name    : AvramDividend.Classical.avram_a40_original_actual_stop_uniform_discounted_gaussian_crossing_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:39:01.445403+00:00
-- url     : https://prove2.me/theorems/8da853e0-a87f-47c8-a7cc-d01cb8df1501
-- title:
--   Actual original stopped canonical Gaussian finitecap discounted positive crossing error vanishes on full reserve band
-- statement:
--   For the exact original ν=0 Gaussian Lévy X stopped at measurable bounded random clock ρ, and genuine physical uniform-mesh index i_m whose cell includes ρ, show the discounted expected positive caplinear spatial crossing error tends to zero across the full bounded reserve band including ruin contact. Use Proved a38 original true stopped clock gap plus Proved a36 weighted nonnegative fullband Gaussian L1 result, with constant-in-m measurable discount ρ. No artificial martingale or assumed expected cash bound.
-- source:
--   Original finitecap physical stopped Gaussian random crossing expected discount with true X and original right-stopped clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a40_original_actual_stop_uniform_discounted_gaussian_crossing_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρ : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (i : ℕ → Ω → ℕ)
    (hCell : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i m ω : ℝ≥0) * Δ ≤ ρ ω ∧
        ρ ω ≤ (i m ω : ℝ≥0) * Δ + Δ)
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw0 : 0 ≤ w 0) (hwneg : ∀ z : ℝ, z < 0 → w z = 0)
    (hwcont : ContinuousOn w (Set.Ici 0))
    (y : ℕ → Ω → ℝ)
    (hy : ∀ᵐ ω ∂P, ∀ m, y m ω ∈ Set.Icc 0 c)
    (hMeas : ∀ (m : ℕ), AEStronglyMeasurable (fun ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i m ω : ℝ≥0) * Δ
      max ((if y m ω + (X.X (ρ ω) ω - X.X s ω) ≤ c
        then w (y m ω + (X.X (ρ ω) ω - X.X s ω))
        else w c + (y m ω + (X.X (ρ ω) ω - X.X s ω) - c)) -
        w (y m ω)) 0) P)
    (q : ℝ) (hq : 0 ≤ q)
    (hρmeas : Measurable ρ) :
    Tendsto (fun (m : ℕ) => ∫ ω,
      Real.exp (-(q * (ρ ω : ℝ))) *
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i m ω : ℝ≥0) * Δ
      max ((if y m ω + (X.X (ρ ω) ω - X.X s ω) ≤ c
        then w (y m ω + (X.X (ρ ω) ω - X.X s ω))
        else w c + (y m ω + (X.X (ρ ω) ω - X.X s ω) - c)) -
        w (y m ω)) 0 ∂P) atTop (nhds (0 : ℝ)) := by sorry
