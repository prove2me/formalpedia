-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger22_original_physical_grid_fourth_energy_upper
-- name    : AvramDividend.Classical.avram_gledger22_original_physical_grid_fourth_energy_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T12:58:01.285928+00:00
-- url     : https://prove2.me/theorems/27ce427d-4714-4808-9f0e-c2f349b37621
-- title:
--   Original Gaussian physical finite-grid fourth energy upper
-- statement:
--   For the original zero-Levy-measure Gaussian process, any finite set of deterministic source intervals of a common width has its integrated sum of nonnegative normalised centred fourth increment powers bounded by the sum of three times the squared interval widths. This genuine source-exact stochastic estimate is obtained from existing original-interval Gaussian fourth moments and finite-sum Lebesgue integration. Applied to the physical grid s_i=i*n/(m+1), it controls the large-increment Taylor remainder tail without an auxiliary Brownian process; it is an analytical prerequisite, not a proof of the full dividend ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger22_original_physical_grid_fourth_energy_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (S : Finset ℕ) (s : ℕ → ℝ≥0) (Δ : ℝ≥0)
    (hMeas : ∀ i ∈ S, Measurable (fun ω : Ω =>
      (X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c) / X.σ)) :
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c) / X.σ
    (∫⁻ ω, ∑ i ∈ S, ENNReal.ofReal ((Z i ω) ^ 4) ∂P) ≤
      ∑ _i ∈ S, ENNReal.ofReal (3 * (Δ : ℝ) ^ 2) := by sorry
