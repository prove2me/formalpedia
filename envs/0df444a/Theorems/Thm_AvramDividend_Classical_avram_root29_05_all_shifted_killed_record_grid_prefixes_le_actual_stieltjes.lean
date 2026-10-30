-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_all_shifted_killed_record_grid_prefixes_le_actual_stieltjes
-- name    : AvramDividend.Classical.avram_root29_05_all_shifted_killed_record_grid_prefixes_le_actual_stieltjes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:54:13.749996+00:00
-- url     : https://prove2.me/theorems/c0a67595-8cd4-49a8-b65e-981f7a653b6d
-- title:
--   All sampled killed shifted future cashflows bounded by actual Stieltjes reward
-- statement:
--   For the true shifted running-supremum dividend measure of any original spectrally negative Lévy future and every nonnegative discount parameter, the supremum over rational killed finite-record cash meshes is at most the actual strictly stopped Stieltjes regulator payment integral.
-- source:
--   Use Proved finite shifted killed record-grid lower bound with each denominator n+1>0 and take successive suprema. This is the lower inequality in the actual shifted reward reconstruction.

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_killed_record_grid_prefix_le_actual_stieltjes

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- Every strictly killed sampled future-record cash prefix is dominated
by the actual continuous-time shifted Stieltjes regulator reward. -/

theorem AvramDividend.Classical.avram_root29_05_all_shifted_killed_record_grid_prefixes_le_actual_stieltjes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (age : ℝ≥0)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q) :
    let M : ℝ≥0 → ℝ := fun v =>
      sSup ((fun w : ℝ≥0 => X.X (age + w) ω - X.X age ω) '' Icc 0 v)
    let μ : Measure ℝ := dividendMeasure (fun r (_ : Ω) => M r) ω
    (⨆ n : ℕ, ⨆ N : ℕ,
      let grid : ℕ → ℝ := fun j =>
        (((j : ℝ≥0) * ((n + 1 : ℕ) : ℝ≥0)⁻¹) : ℝ)
      ∑ k ∈ Finset.range N,
        if ENNReal.ofReal (grid (k + 1)) < τ then
          ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) *
            ENNReal.ofReal
              (M (grid (k + 1)).toNNReal - M (grid k).toNNReal)
        else 0) ≤
    (∫⁻ r in paymentTimes τ,
      if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0 ∂μ) := by sorry
