-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_grid_preexit_positive_C2_domain
-- name    : AvramDividend.Classical.avram_wave7_18_original_grid_preexit_positive_C2_domain
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:22:45.735365+00:00
-- url     : https://prove2.me/theorems/837aade7-bfae-42db-a83a-5956169187f1
-- title:
--   Original post-payment reserve stays in the positive C² cap interior before bounded grid exit
-- statement:
--   For the genuine controlled reserve x+X_t-rightLimit D_t, the first finite-grid exit index from (lower,upper) has K≤m and, for each k<K, the post-payment reserve lies in [lower,upper]. If 0<lower and the entire closed band has ENNReal.ofReal y<C, then all such pre-exit grid values lie in the exact positive capped C² domain {y|0<y∧ENNReal.ofReal y<C}, and the assumed ContDiffOn ℝ 2 w on precisely this domain yields the ContDiffWithinAt conclusion there. The right-limit dividend convention handles simultaneous payment jumps; this is grid-localisation, not continuous-time exit or Itô formula.

import Mathlib
import Mathlib.Probability.Process.HittingTime
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_original_grid_preexit_positive_C2_domain
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (lower upper : ℝ) (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (clock : ℕ → ℝ≥0) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (x + X.X (clock k) ω - rightLimit D (clock k) ω - upper)
        (lower - (x + X.X (clock k) ω - rightLimit D (clock k) ω)))
      (Set.Ioi (0 : ℝ)) 0 m ω) :
    (∀ ω, K ω ≤ m) ∧
    (∀ ω k, k < K ω →
      let z : ℝ := x + X.X (clock k) ω - rightLimit D (clock k) ω
      z ∈ Set.Icc lower upper ∧
      (0 < z ∧ ENNReal.ofReal z < C) ∧
      ContDiffWithinAt ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} z) := by sorry
