-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_compensated_taylor_L2
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_compensated_taylor_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:02:19.032196+00:00
-- url     : https://prove2.me/theorems/b62df142-de27-4678-9eb2-f357de1c687d
-- title:
--   Actual ruin-stopped compensated nonlinear Lévy jump Taylor kernel has finite predictable L2 energy
-- statement:
--   For the original spectrally negative Lévy process, an adapted dividend strategy and a C² test function on a compact interior reserve band, the nonlinear Taylor remainder of each negative source jump after the exact small-jump linear correction remains predictable and square-integrable against the actual Lévy jump intensity after stopping at the genuine controlled ruin time. This is an L² prerequisite for a compensated small-jump limit; it does not assert the martingale compensation identity or the full Itô–Meyer formula.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4, stopped nonlinear jump correction. Exact original source prepayment reserve, genuine controlled ruinTime, proved 04b compensated full negative-mark predictable L² energy (67a347f4-b864-4fc8-9dec-0d09777d91dd), right-continuous stopping time (0e921b75-8854-48dd-81ae-f0a62352256d), and inclusive-survival strong predictability (69806d16-1c2a-445a-920f-4500f3645d6a). This isolates the essential stopped Taylor kernel without assuming independence of D and X or substituting an abstract Poisson space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_compensated_taylor_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] HS ∧
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((HS (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤ := by sorry
