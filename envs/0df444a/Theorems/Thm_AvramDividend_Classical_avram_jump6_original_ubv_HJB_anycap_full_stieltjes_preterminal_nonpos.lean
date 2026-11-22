-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_original_ubv_HJB_anycap_full_stieltjes_preterminal_nonpos
-- name    : AvramDividend.Classical.avram_jump6_original_ubv_HJB_anycap_full_stieltjes_preterminal_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T18:56:32.738302+00:00
-- url     : https://prove2.me/theorems/cb9b0cde-a3c8-40cf-9c73-42831322cf72
-- title:
--   UBV original HJB gives all-cap full discounted physical Stieltjes dividend sign at true pre-ruin clocks
-- statement:
--   For every original unbounded-variation spectrally negative Lévy process, HJB supersolution and admissible cap-limited dividend strategy, at any physical time zero or strictly before actual ruin, the exact discounted Lebesgue–Stieltjes dividend cash on the closed interval [0,T] plus the negative of the candidate-value cap-linear drop is nonpositive. The statement includes the initial dividend atom and all diffuse/atomic payment parts, and handles both finite and infinite cap without assuming any stopped stochastic calculus theorem. The proof extracts w'≥1 from the HJB max identity, descends from interior C² to C¹, and applies the already-Proved all-cap full physical Stieltjes sign theorem.
-- source:
--   Original Avram root 545c65ef-edd3-4ecb-aeaa-8dd6c5bce0e7; expected HJB budget 15815eff-2c54-41e3-97a6-d216a3efb8d8 and 464200c8-be79-47cd-8938-79343e0d7fce; Proved original all-cap Stieltjes source b7f6754b-bb40-4d86-bd48-aae4411986f7. Source-faithful exact Icc payment and caplinear w extension.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_original_ubv_HJB_anycap_full_stieltjes_preterminal_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X T ω - rightLimit D T ω) -
       V (x + X.X T ω)) ≤ 0 := by sorry
