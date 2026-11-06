-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_clock_compact_signed_budget
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_clock_compact_signed_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:50:43.443223+00:00
-- url     : https://prove2.me/theorems/45626124-3b7e-489d-a249-165f2bf47acd
-- title:
--   Actual original BV ruin-stopped predictable compact band has signed compensated HJB nonpositive mean
-- statement:
--   The actual original Lévy X and admissible D automatically supply a bounded ruin-truncated stopping time and a predictable compact pre-reserve band, then the literal original compensated jump plus HJB drift is jointly L1 with nonpositive expected sum. The stopping, predictable and strip hypotheses are discharged from accepted original source localisation, not postulated. This is an interior signed grid building block; finite-mesh cash inequality, boundary passage and Fatou remain independent.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_admissible_BV_ruin_compact_C1_jump_hypotheses
import Theorems.Thm_AvramDividend_Classical_avram_p3_e2_original_signed_M_plus_B_expected_budget_interior
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_clock_compact_signed_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (T : ℝ≥0) (a b : ℝ)
    (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hBand : Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
         w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
    let F : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift * deriv w (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) +
         (∫ z in Iio (0 : ℝ),
            w (Function.leftLim
              (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 + z) -
            w (Function.leftLim
              (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) -
         q * w (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1))
      else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict
        {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let M : Ω → ℝ := fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))
    let B : Ω → ℝ := fun ω =>
      ∫ t, F (t, ω)
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)
    Integrable (fun ω => M ω + B ω) P ∧
      (∫ ω, M ω + B ω ∂P) ≤ 0 := by sorry
