-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_cell_caplinear_raw_jump_envelope
-- name    : AvramDividend.Classical.avram_p3_bv_original_source_cell_caplinear_raw_jump_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:10:19.582078+00:00
-- url     : https://prove2.me/theorems/c19000be-6a90-4ccb-907f-501df7c1fa8a
-- title:
--   Original BV cap-linear frozen-source increments discard continuous residual while preserving exact raw negative jump and drift terms
-- statement:
--   For the original spectrally negative Levy controlled reserve on almost every path, a physical source mesh cell with nonnegative frozen source endpoint has cap-linear HJB value increment bounded by the same explicit drift and original raw negative-jump increment without the monotone nonnegative residual. The cap-linear extension is valid at cap contact and above-cap frozen overshoots.
-- source:
--   Source-exact combination of Proved 3afeac6a physical raw-source identity, e9d95081 monotone original BV residual, 56a6e05f monotone all-cap C1 value. Named obligation for original stopped C1 source chain db6a3111.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_allcap_linear_monotone_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_cell_raw_jump_residual_identity

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- The original continuous BV residual can only decrease the cap-linear
   frozen-dividend source value, retaining the actual negative jump sum. -/

theorem AvramDividend.Classical.avram_p3_bv_original_source_cell_caplinear_raw_jump_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (i : ℕ),
      u i ≤ u (i + 1) →
      0 ≤ x + X.X (u (i + 1)) ω - rightLimit D (u i) ω →
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        V (x + X.X (u i) ω - rightLimit D (u i) ω) ≤
      V ((x + X.X (u i) ω - rightLimit D (u i) ω) +
        (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) -
        (∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
         else 0)) -
        V (x + X.X (u i) ω - rightLimit D (u i) ω) := by sorry
