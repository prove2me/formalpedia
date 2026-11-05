-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_negative_raw_jump_grid_caplinear_eq_w
-- name    : AvramDividend.Classical.avram_p3_2_original_negative_raw_jump_grid_caplinear_eq_w
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:34:33.771801+00:00
-- url     : https://prove2.me/theorems/6dcd41e4-bc6e-4ec4-927a-0a0ef55ac409
-- title:
--   Original nonpositive jump cap-linear grid equals exact w nonlinear negative-jump source
-- statement:
--   On any nondecreasing original physical time grid whose left postpayment reserves are at or below the finite cap, the discounted cap-linear negative-jump sum agrees exactly with the original w nonlinear negative-jump sum. Each raw original Lévy jump interval has nonnegative loss, so its source change is nonpositive and never requires w beyond the cap. This exposes the exact jump term needed by the predictable Lévy compensator.
-- source:
--   Source-exact finite-grid use of Proved original raw negative-jump interval nonnegative 017d744a and cap-linear frozen nonpositive step 811e62ab, with a separate explicit original pre-grid reserve cap hypothesis to discharge under admissibility/localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_negative_jump_tsum_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_frozen_nonpositive_jump_cap_step

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_negative_raw_jump_grid_caplinear_eq_w
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (q : ℝ)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u)
    (hCap : ∀ i : ℕ, i < n →
      C = ⊤ ∨ x + X.X (u i) ω - rightLimit D (u i) ω ≤ C.toReal) :
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
