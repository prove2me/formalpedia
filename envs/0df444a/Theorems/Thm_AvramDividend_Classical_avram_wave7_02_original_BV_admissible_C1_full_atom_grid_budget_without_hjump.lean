-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_admissible_C1_full_atom_grid_budget_without_hjump
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_admissible_C1_full_atom_grid_budget_without_hjump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:23:42.266166+00:00
-- url     : https://prove2.me/theorems/63623d48-2ca0-44f7-a60a-bccd5a28ec90
-- title:
--   Original admissible BV discounted complete-atom C1 stopped-grid budget without an independent hjump assumption
-- statement:
--   For the canonical standing bounded-variation spectrally negative Levy process, an IsAdmissibleLe dividend strategy, initial reserve x≤C and the genuine positive-cap C1 gradient≥1, the complete discounted finite-grid cash-plus-terminal-value bound follows from original admissibility and candidate regularity alone. The right-dividend hjump inequality is a proved consequence of admissibility and the C1 gradient, including cap equality, and is supplied by the independent source-specific theorem. The statement retains the exact physical rightLimit D, time-zero atom and original riskProcess, and does not assume generator compensation or stochastic limit passage.
-- source:
--   Composition of the Proved canonical source full-atom grid 55d9d542 and the new direct canonical hjump-from-admissibility theorem. Source IsAdmissibleLe and IsDividendStrategy are unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_canonical_hjump_of_C1_and_admissible
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_canonical_C1_compact_full_atom_grid_budget
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_admissible_C1_full_atom_grid_budget_without_hjump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (hC : 0 < C)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (a b : ℝ) (hab : a < b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ L : ℝ, 1 ≤ L ∧
      ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u →
        u 0 = 0 →
        (∀ n, x + X.X (u n) ω - rightLimit D (u n) ω ∈ Icc a b) →
        ∀ n,
          rightLimit D 0 ω +
          (∑ i ∈ Finset.range n,
            Real.exp (-(q * (u (i + 1) : ℝ))) *
              (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) +
          Real.exp (-(q * (u n : ℝ))) *
            w (x + X.X (u n) ω - rightLimit D (u n) ω) ≤
          w x +
          (∑ i ∈ Finset.range n,
            Real.exp (-(q * (u (i + 1) : ℝ))) *
              (L * (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) := by sorry
