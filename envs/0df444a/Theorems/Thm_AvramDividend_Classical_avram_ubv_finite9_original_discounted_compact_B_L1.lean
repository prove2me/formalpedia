-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_discounted_compact_B_L1
-- name    : AvramDividend.Classical.avram_ubv_finite9_original_discounted_compact_B_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:56:20.181909+00:00
-- url     : https://prove2.me/theorems/53ea8e25-4309-4d30-ac85-55cef3c119d7
-- title:
--   Physical finite-cap compensated-Taylor compact generator drift B is integrable
-- statement:
--   The exact finite-horizon discounted generator drift term appearing in the original stopped compensated-Taylor and HJB source has finite expectation when its interior event is the original pre-right-payment reserve lying inside the compact strip and the cap is finite. This is a pointwise identification with the inclusive stopped discounted predictable generator at a deterministic terminal time; all ruin guarding, real discounting and original time measure are preserved. The complete Ito-Meyer dividend cash budget is separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_discounted_compact_stopped_generator_L1

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_original_discounted_compact_B_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D)
    (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u v δ : ℝ) (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C.toReal) (T : ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let E : Set (ℝ≥0 × Ω) := {p | Y p ∈ Icc (u + δ) v}
    let B : Ω → ℝ := fun ω => ∫ t : ℝ≥0,
      (if (t, ω) ∈ E then
        (if t ≤ T then Real.exp (-(q * (t : ℝ))) else 0) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0) *
          (X.generator w (Y (t, ω)) - q * w (Y (t, ω)))
      else 0)
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)
    Integrable B P := by sorry
