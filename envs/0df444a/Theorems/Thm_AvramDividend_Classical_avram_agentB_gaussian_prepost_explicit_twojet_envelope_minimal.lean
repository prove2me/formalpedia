-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentB_gaussian_prepost_explicit_twojet_envelope_minimal
-- name    : AvramDividend.Classical.avram_agentB_gaussian_prepost_explicit_twojet_envelope_minimal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T10:13:00.54726+00:00
-- url     : https://prove2.me/theorems/d4cc3b49-427d-43cc-a65f-f4fd7261ea79
-- title:
--   Minimal original Gaussian true-reserve same-grid absolute two-jet dividend bound
-- statement:
--   For the actual spectrally negative Levy path X and original dividend strategy D, the absolute difference between Gaussian first/second Hermite physical-grid sums evaluated at pre-dividend versus postright-dividend reserve is bounded at every mesh and path by the explicit sum of absolute derivative and Hessian coefficient differences weighted by centred Gaussian increments. Pure finite-sum algebra using the already proved two-jet bound, with exact active stopped-cell predicate.
-- source:
--   Proved avram_agentB_original_samegrid_Gaussian_twojet_finite_abs_envelope and Finset.sum_sub_distrib under exact original X,D physical grid.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_agentB_gaussian_prepost_explicit_twojet_envelope_minimal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (ρ : Ω → ℝ≥0) :
    let M : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
          let s : ℝ≥0 := (i : ℝ≥0) * Δ
          if s < ρ ω then
            let y := riskProcess X x D s ω
            let Z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
            Real.exp (-(q * (s : ℝ))) *
              (deriv w y * Z +
                (iteratedDeriv 2 w y / 2) * (Z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
          else 0
    let N : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          let y := x + X.X s ω - rightLimit D s ω
          let Z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
          Real.exp (-(q * (s : ℝ))) *
            (deriv w y * Z +
              (iteratedDeriv 2 w y / 2) * (Z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
        else 0
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let Z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        let U := Z ^ 2 - (Δ : ℝ) * X.σ ^ 2
        let ypost := x + X.X s ω - rightLimit D s ω
        let ypre := riskProcess X x D s ω
        let e : ℝ := if s < ρ ω then Real.exp (-(q * (s : ℝ))) else 0
        |e| * (|deriv w ypost - deriv w ypre| * |Z| +
          |iteratedDeriv 2 w ypost / 2 - iteratedDeriv 2 w ypre / 2| * |U|)
    ∀ m : ℕ, ∀ ω : Ω, |N m ω - M m ω| ≤ E m ω := by sorry
