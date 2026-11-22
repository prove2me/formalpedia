-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_discounted_gaussian_full_grid_sqrt_rate
-- name    : AvramDividend.Classical.avram_lsv_original_preruin_discounted_gaussian_full_grid_sqrt_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:30:59.745223+00:00
-- url     : https://prove2.me/theorems/2fa934ef-46c8-4ddc-9fa3-a3754405d0c2
-- title:
--   Original true pre-ruin discounted dividend atom times Gaussian future increments entire physical grid root-rate
-- statement:
--   For actual original jumpfree Gaussian spectrally negative Levy source and actual admissible dividend strategy, the total discounted right-dividend atom weighted absolute centred Gaussian increment over a full physical mesh is integrable. Its expectation has a deterministic uniform rate O(sqrt(n/(m+1))) using source exact rightCont stopped weighted cell first moment and original finite-grid pre-ruin dividend mass expected bound. This supplies the core stochastic half of original prepayment-postpayment first Hermite mesh target 0326fd9f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_dividend_gaussian_future_weighted_cell_L1
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_rightcont_discounted_preruin_single_atom_L2
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_discounted_rightatoms_expected_mass_L1
import Theorems.Thm_AvramDividend_Classical_avram_agentB_gaussian_weighted_first_absolute_moment_grid_integral_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_prehorizon_grid_le
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
noncomputable section

theorem AvramDividend.Classical.avram_lsv_original_preruin_discounted_gaussian_full_grid_sqrt_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hBV : ¬ X.BoundedVariation) (hσ : 0 < X.σ)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (q : ℝ) (hq : 0 ≤ q) :
    let V : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let H : ℝ := if s < ρ ω then
          Real.exp (-(q * (s : ℝ))) *
            (rightLimit D s ω - D s ω)
          else 0
        let Z : ℝ := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        H * |Z|
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ m, Integrable (V m) P) ∧
      ∀ m : ℕ,
        (∫ ω, V m ω ∂P) ≤
          K * Real.sqrt ((n : ℝ) / ((m + 1 : ℕ) : ℝ)) := by sorry
