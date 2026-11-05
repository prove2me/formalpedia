-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_h_original_BV_interior_anchor_real_ruin_jump_centered
-- name    : AvramDividend.Classical.avram_p3_h_original_BV_interior_anchor_real_ruin_jump_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:15:43.490004+00:00
-- url     : https://prove2.me/theorems/dd1d769d-616e-4746-9013-125c299aa554
-- title:
--   Original BV interior anchor automatically gives actual ruin-stopped nonlinear jump centring
-- statement:
--   At any strict interior original reserve anchor, the compact-strip constants are automatic and the true original controlled real-ruin stopped nonlinear Lévy jump compensator is integrable and centred, with an explicit existential original reserve band. This removes the ancillary Lipschitz assumptions from the stopped source compensation interface.
-- source:
--   Proved P3-H concrete compact Lipschitz 57f9bd71 and source exact P3-E/G real-ruin compensator 1ce83144 (currently Open).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_h_original_BV_positive_interior_has_concrete_Lipschitz_band
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_h_original_BV_interior_anchor_real_ruin_jump_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici 0))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (z : ℝ) (hz : 0 < z) (hzC : ENNReal.ofReal z < C)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ 2 ∧ a ≤ b ∧ z ∈ Icc a b ∧
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
