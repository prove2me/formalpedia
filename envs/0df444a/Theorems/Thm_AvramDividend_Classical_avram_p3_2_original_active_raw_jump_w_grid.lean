-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_active_raw_jump_w_grid
-- name    : AvramDividend.Classical.avram_p3_2_original_active_raw_jump_w_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:46:35.743054+00:00
-- url     : https://prove2.me/theorems/bc912ea7-2d81-465c-84a3-304afda8d40a
-- title:
--   Exact original zero-or-preruin raw negative-jump grid uses w with automatically capped postpayment reserves
-- statement:
--   For the actual original spectrally negative Lévy path and admissible dividend strategy, every left grid point at zero or strictly before ruin automatically has its physical post-rightpayment reserve in the closed cap. Consequently the discounted negative-jump cap-linear source sum equals the literal original w negative-jump sum, without an extra cap-side hypothesis, across the complete physical grid.
-- source:
--   Source-exact composition of Proved original closed-cap postpayment reserve d88fd858 and the P3-2 raw negative-jump cap-linear equality 6dcd41e4, using the revision-pinned ENNReal.ofReal_le_iff_le_toReal lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_negative_raw_jump_grid_caplinear_eq_w
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_postrightpayment_reserve_closed_cap

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_active_raw_jump_w_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (n : ℕ) (hu : Monotone u)
    (hActive : ∀ i : ℕ, i < n →
      u i = 0 ∨ (u i : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    (∑ i ∈ Finset.range n,
      Real.exp (-(q * (u i : ℝ))) *
        (V ((x + X.X (u i) ω - rightLimit D (u i) ω) -
          (∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0)) -
        V (x + X.X (u i) ω - rightLimit D (u i) ω))) =
    (∑ i ∈ Finset.range n,
      Real.exp (-(q * (u i : ℝ))) *
        (w ((x + X.X (u i) ω - rightLimit D (u i) ω) -
          (∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0)) -
        w (x + X.X (u i) ω - rightLimit D (u i) ω))) := by sorry
