-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_actual_capped_stopped_bracket_le_deterministic
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_actual_capped_stopped_bracket_le_deterministic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:59:39.446269+00:00
-- url     : https://prove2.me/theorems/802255db-f5d3-407d-a995-b26826841431
-- title:
--   True original Gaussian bracket stopped at any capped clock has deterministic bound
-- statement:
--   The original finite-horizon masked Gaussian energy bracket, stopped at an arbitrary original-clock time capped by the horizon, is pointwise dominated by a deterministic constant independent of the sample path. This uses actual original process integrability and no stopped-process substitution or filtration augmentation.
-- source:
--   Previously Proved Gaussian10 actual finite-horizon energy and deterministic terminal cap; Proved d7cfc4ba original capped ruin-clock monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_actual_masked_square_energy_integrableOn
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_actual_masked_square_bracket_le_deterministic
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_capped_ruin_bracket_le_horizon

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_actual_capped_stopped_bracket_le_deterministic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (μtime : Measure ℝ≥0) (T : ℝ≥0)
    (hFinite : μtime (Ioc (0 : ℝ≥0) T) < ⊤)
    (τ : Ω → ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω,
      (∫ t in Ioc (0 : ℝ≥0) (min (τ ω) T),
        (G (t, ω)) ^ 2 ∂μtime) ≤
      C ^ 2 * (μtime.restrict (Ioc (0 : ℝ≥0) T)).real Set.univ := by sorry
