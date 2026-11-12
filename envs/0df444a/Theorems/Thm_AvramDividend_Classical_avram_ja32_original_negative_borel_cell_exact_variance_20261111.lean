-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja32_original_negative_borel_cell_exact_variance_20261111
-- name    : AvramDividend.Classical.avram_ja32_original_negative_borel_cell_exact_variance_20261111
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T22:11:39.117997+00:00
-- url     : https://prove2.me/theorems/6f4dddb6-8717-4eeb-beae-f536fefb0b0d
-- title:
--   Exact physical Poisson variance of one arbitrary original negative Borel jump-mark cell
-- statement:
--   On the literal finite-activity spectrally negative Lévy process, the centred count of jumps having a mark in any measurable negative Borel set has square expectation t ν(B) and integrable square. This is the true-source diagonal moment needed for finite Borel mark partition isometry.
-- source:
--   True-source physical Poisson random measure moment bridge for JA30 finite Borel partition. Different from harmonic-annulus-only moments; needs within-annulus Borel control.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja32_original_negative_borel_cell_exact_variance_20261111
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    let Y : Ω → ℝ := fun ω =>
      (NX ω (Ioc 0 T ×ˢ B)).toReal - r
    Integrable (fun ω => (Y ω) ^ 2) P ∧
      (∫ ω, (Y ω) ^ 2 ∂P) = r := by sorry
