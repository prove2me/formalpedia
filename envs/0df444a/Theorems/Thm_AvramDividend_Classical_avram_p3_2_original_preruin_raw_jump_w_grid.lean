-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_preruin_raw_jump_w_grid
-- name    : AvramDividend.Classical.avram_p3_2_original_preruin_raw_jump_w_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:01:13.936294+00:00
-- url     : https://prove2.me/theorems/e81e076f-4d3a-4b5c-9ac4-96a8c7a5831e
-- title:
--   Original physical stopped pre-ruin grid automatically has exact w negative-jump source sums
-- statement:
--   For an original capped admissible dividend control, the source stopped grid begins at zero and each right endpoint lies at zero or strictly before ruin. This guarantees the left endpoint active condition, hence the real discounted cap-linear raw-jump sum equals the literal original w negative-jump sum. It preserves zero, ruin and cap boundary conditions and uses only the proved active-grid theorem.
-- source:
--   P3-2 original pre-ruin endpoint to active-left endpoint adapter; applies the source-exact cap-linear jump identity and admissible closed-cap reserve bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_active_raw_jump_w_grid

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_preruin_raw_jump_w_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨ (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
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
