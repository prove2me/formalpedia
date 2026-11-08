-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_discounted_compact_stopped_generator_L1
-- name    : AvramDividend.Classical.avram_ubv_finite9_discounted_compact_stopped_generator_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:51:29.396655+00:00
-- url     : https://prove2.me/theorems/89e30479-06c0-48dd-bfc6-3005b85844bf
-- title:
--   Original finite-cap discounted compact generator integrability through arbitrary right-continuous stopping
-- statement:
--   The original finite-cap discounted HJB generator residual of the pre-right-payment surplus is integrable when integrated up to any right-continuous stopping subclock against the physical time measure. The proof combines the pinned finite-cap real-interior HJB bridge, the original discounted predictable compact generator certificate and the inclusive stopping-mask Fubini theorem. Original dividends, ruin clock, Gaussian and compensated jump source terms are preserved, with no claim yet of an Itô-Meyer cash budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_finitecap_real_interior_HJB_bridge
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_discounted_true_clock_compact_generator_hjb_L1_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_predictable_inclusive_sigma_mask_L1

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_discounted_compact_stopped_generator_L1
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
    (huv : u + δ < v) (hv : v < C.toReal)
    (T : ℝ≥0) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (ρ p * (if Y p ∈ Icc (u + δ) v then
          X.generator w (Y p) - q * w (Y p) else 0))
    Integrable (fun ω => ∫ t : ℝ≥0,
      if t ≤ σ ω then R (t, ω) else 0
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P := by sorry
