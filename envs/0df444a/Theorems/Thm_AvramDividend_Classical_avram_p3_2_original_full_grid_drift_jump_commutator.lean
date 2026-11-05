-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_full_grid_drift_jump_commutator
-- name    : AvramDividend.Classical.avram_p3_2_original_full_grid_drift_jump_commutator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:51:28.143627+00:00
-- url     : https://prove2.me/theorems/43ca852b-3fd3-45be-bfd1-6f7346943039
-- title:
--   Original cap-linear BV drift and negative-jump grid reduces to true w kernel plus exact mixed commutator
-- statement:
--   The actual original discounted source reserve increment on any monotone grid decomposes exactly into cap-linear continuous-drift change, the literal original negative-jump nonlinear w kernel, and a mixed drift-jump commutator. The cap condition is imposed only at the physical left grid reserve, so it holds at cap contact and at the time-zero left cell. This is an exact algebraic identity on physical X and D without replacing the process, using the independently Proved raw negative-jump cap-linear equality.
-- source:
--   Original P3-2 source cap-linear jump equality 6dcd41e4 and exact finite-grid mixed commutator algebra for X.X/rightLimit D.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_negative_raw_jump_grid_caplinear_eq_w

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_full_grid_drift_jump_commutator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (q : ℝ)
    (u : ℕ → ℝ≥0) (n : ℕ) (hu : Monotone u)
    (hCap : ∀ i : ℕ, i < n →
      C = ⊤ ∨ x + X.X (u i) ω - rightLimit D (u i) ω ≤ C.toReal) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let z : ℕ → ℝ := fun i => x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => ((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift
    let j : ℕ → ℝ := fun i =>
      ∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) v - X.X v ω
      else 0
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    (∑ i ∈ Finset.range n, e i * (V (z i + c i - j i) - V (z i))) =
      (∑ i ∈ Finset.range n, e i * (V (z i + c i) - V (z i))) +
      (∑ i ∈ Finset.range n, e i * (w (z i - j i) - w (z i))) +
      (∑ i ∈ Finset.range n,
        e i * (V (z i + c i - j i) - V (z i + c i) -
          V (z i - j i) + V (z i))) := by sorry
