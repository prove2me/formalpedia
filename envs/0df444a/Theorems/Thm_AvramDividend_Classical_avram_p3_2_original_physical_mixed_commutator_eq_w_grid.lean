-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_mixed_commutator_eq_w_grid
-- name    : AvramDividend.Classical.avram_p3_2_original_physical_mixed_commutator_eq_w_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:11:10.789022+00:00
-- url     : https://prove2.me/theorems/51bae427-5f47-417f-b218-c273208b00df
-- title:
--   Original physical BV mixed raw-jump commutator matches w on cap-safe drift-upshift grids
-- statement:
--   On every original monotone source grid for X and D, if the physical postpayment reserve and its drift-upshift stay inside the closed cap, then the discounted exact cap-linear four-point mixed drift/raw negative-jump commutator coincides with the true w mixed commutator used by F2. Genuine source raw negative-jump cell sums are nonnegative on every path. Valid with cap contacts and negative after-jump reserves, and keeps original physical X/D.
-- source:
--   Composition of original raw-negative-jump nonnegativity 017d744a and P3-2 cap-linear mixed commutator below-cap identity; exact physical left reserve and drift/jump cells.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_negative_jump_tsum_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_caplinear_mixed_commutator_eq_w_of_upshift_below_cap

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_physical_mixed_commutator_eq_w_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (q : ℝ)
    (u : ℕ → ℝ≥0) (n : ℕ) (hu : Monotone u)
    (hCap : ∀ i : ℕ, i < n →
      C = ⊤ ∨ x + X.X (u i) ω - rightLimit D (u i) ω ≤ C.toReal)
    (hUp : ∀ i : ℕ, i < n →
      C = ⊤ ∨ x + X.X (u i) ω - rightLimit D (u i) ω +
        (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) ≤ C.toReal) :
    let V : ℝ → ℝ := fun r =>
      if C = ⊤ then w r else if r ≤ C.toReal then w r
      else w C.toReal + (r - C.toReal)
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i =>
      (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift)
    let j : ℕ → ℝ := fun i =>
      ∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) v - X.X v ω
      else 0
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    (∑ i ∈ Finset.range n,
      e i * (V (z i + c i - j i) - V (z i + c i) -
        V (z i - j i) + V (z i))) =
    (∑ i ∈ Finset.range n,
      e i * (w (z i + c i - j i) - w (z i + c i) -
        w (z i - j i) + w (z i))) := by sorry
