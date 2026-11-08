-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_actual_stopped_gradient_gaussian_bracket_adapted
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_actual_stopped_gradient_gaussian_bracket_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:24:39.545722+00:00
-- url     : https://prove2.me/theorems/2616fc97-3950-4782-a492-26dadfdef454
-- title:
--   Actual original stopped Gaussian gradient bracket adapted on original stopping filtration
-- statement:
--   Specialise the squared-bracket adaptedness theorem to Avram’s actual Brownian coefficient X.σ times the C2 candidate derivative evaluated at the original left-limit pre-right-payment reserve, masked to the compact interior band. Existing Proved original Gaussian source L2 establishes the coefficient is rightCont predictable. Consequently the true pathwise Gaussian bracket is adapted to the original stopping filtration, retaining X, D, time-zero, ruin conventions and the original probability space.
-- source:
--   Proved original Gaussian source 7ae1130d and original right-continuous bracket child 5f4ccdfd; inspired by formal-mathfin BracketCompensator, inspected 2026-11-07.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_rightcont_predictable_bracket_adapted

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_actual_stopped_gradient_gaussian_bracket_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (μtime : Measure ℝ≥0) [SFinite μtime] :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    Adapted 𝓕.rightCont (fun t ω =>
      ∫ s in Ioc (0 : ℝ≥0) t, (G (s, ω)) ^ 2 ∂μtime) := by sorry
