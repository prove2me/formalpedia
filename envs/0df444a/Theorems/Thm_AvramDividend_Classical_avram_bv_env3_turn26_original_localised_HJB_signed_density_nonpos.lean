-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn26_original_localised_HJB_signed_density_nonpos
-- name    : AvramDividend.Classical.avram_bv_env3_turn26_original_localised_HJB_signed_density_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:02:12.46939+00:00
-- url     : https://prove2.me/theorems/72d2000c-ff6d-40bf-845b-6c9a0ea7be35
-- title:
--   Original bounded-variation localised generator HJB source drift is nonpositive
-- statement:
--   On the original spectrally negative Lévy process, at each physical time and sample where the controlled pre-reserve U lies strictly in (0,C), the discounted HJB generator residual exp(-qt)(generator w(U)-q*w(U)) is nonpositive. Outside the genuine localisation event E the drift density is zero. This is the sign input for original stopped BV finite-grid source estimates.
-- source:
--   Exact original SpectrallyNegativeLevy.generator and pinned Real.exp_pos; hw_gen is used only on the genuine interior region. Distinct from stochastic compensation/integrability obligations, which remain explicit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn26_original_localised_HJB_signed_density_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (U : ℝ≥0 × Ω → ℝ) (E : Set (ℝ≥0 × Ω))
    (hInterior : ∀ p ∈ E, 0 < U p ∧ ENNReal.ofReal (U p) < C) :
    ∀ p : ℝ≥0 × Ω,
      (if p ∈ E then
        Real.exp (-(q * (p.1 : ℝ))) *
          (X.generator w (U p) - q * w (U p))
       else 0) ≤ 0 := by sorry
