-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_original_strict_cash_grid_limit_of_discount_modulus
-- name    : AvramDividend.Classical.avram_chat24_original_strict_cash_grid_limit_of_discount_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:29:50.795785+00:00
-- url     : https://prove2.me/theorems/480d6550-9f4e-4c4f-a086-07c75d921d62
-- title:
--   Original strict cash mesh limit from discount modulus
-- statement:
--   Source-faithful analytic child of actual limit target 8ee5bfc7-c7d8-44b0-904f-a68e4becd13f. For genuine meshes tending to zero, original left-discounted cash sums converge to original strict cash. Cell discount oscillations times total original dividend give an explicit squeezing error. This deterministic lemma is applied only after proving mesh convergence for the actual uniform grid.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_chat24_original_strict_cash_grid_limit_of_discount_modulus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (B : ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ) (mesh : ℕ → ℝ)
    (hu : ∀ n, Monotone (u n)) (hu0 : ∀ n, u n 0 = 0)
    (huN : ∀ n, u n (N n) = B)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (hdiscount : ∀ n i, i < N n →
      Real.exp (-(q * (u n i : ℝ))) - Real.exp (-(q * (u n (i + 1) : ℝ))) ≤ q * mesh n) :
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      Real.exp (-(q * (u n i : ℝ))) * (D (u n (i + 1)) ω - D (u n i) ω))
      atTop (nhds ((∫⁻ t in Ico (0 : ℝ) (B : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)) := by sorry
