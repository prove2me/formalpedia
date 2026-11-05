-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_h_original_BV_finite_mesh_real_ruin_jump_centered
-- name    : AvramDividend.Classical.avram_p3_h_original_BV_finite_mesh_real_ruin_jump_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:21:23.39945+00:00
-- url     : https://prove2.me/theorems/c5d9c323-d494-46d2-aaf4-7e72e9624b3e
-- title:
--   Actual original BV finite reserve mesh has one stopped nonlinear jump compensation mean-zero witness
-- statement:
--   All finitely many strict positive-cap original BV reserve states can be localised by a single band with uniform C1 Lipschitz and value constants; the actual original ruin-stopped negative jump compensation on this band is L1 and has zero mean.
-- source:
--   Proved P3-H finite mesh uniform Lipschitz and source-exact original P3-E/G ruin-stopped nonlinear compensator 1ce83144 (Open child).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_h_original_BV_finite_mesh_real_ruin_jump_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici 0))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (S : Finset ℝ) (hS : S.Nonempty)
    (hInside : ∀ z ∈ S, 0 < z ∧ ENNReal.ofReal z < C)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ 2 ∧ a ≤ b ∧
      (∀ z ∈ S, z ∈ Icc a b) ∧
      let τ : Ω → ℝ≥0 := fun ω =>
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let E : Set (ℝ≥0 × Ω) := {p |
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        if p.1 ∈ E ∧ p.2 < 0 then
          Real.exp (-(q * (p.1.1 : ℝ))) *
            (w (Function.leftLim (fun s : ℝ≥0 =>
              x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
             w (Function.leftLim (fun s : ℝ≥0 =>
              x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
        else 0
      let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
      Integrable (fun ω =>
        (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
        (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
            Real.toNNReal))) P ∧
      (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
        (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
            Real.toNNReal))) ∂P) = 0  := by sorry
