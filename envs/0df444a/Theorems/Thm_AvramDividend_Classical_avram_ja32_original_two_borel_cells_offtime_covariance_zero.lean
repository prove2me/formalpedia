-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja32_original_two_borel_cells_offtime_covariance_zero
-- name    : AvramDividend.Classical.avram_ja32_original_two_borel_cells_offtime_covariance_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:56:29.702343+00:00
-- url     : https://prove2.me/theorems/d4129097-287a-4abd-8242-8427c02dbdea
-- title:
--   Arbitrary physical past and future Borel mark counts are centred and orthogonal
-- statement:
--   Two original negative Borel marked count increments on disjoint chronological windows have centred cross expectation zero, provided the cells are separated from zero. The result uses source filtration adaptedness, L2 of the original past cell, and compensated conditional mean zero of the original future cell; it makes no independent-spatial-mark assumption.
-- source:
--   Physical temporal pair moment for arbitrary Borel mark-grid cells, prerequisite for original JA28 finite-cutoff marked Gaussian isometry and Borel factorial sandwich.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ja32_original_two_borel_cells_offtime_covariance_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (cutp : ℕ) (Bp : Set ℝ) (hBp : MeasurableSet Bp)
    (hSepP : Bp ⊆ Iic (-(1 / ((cutp : ℝ) + 1))))
    (cutf : ℕ) (ε : ℝ) (hε : 0 < ε)
    (Bf : Set ℝ) (hBf : MeasurableSet Bf)
    (hBandF : Bf ⊆ Ioo (-1 : ℝ) (-ε))
    (hCutF : Bf ⊆ Iic (-(1 / ((cutf : ℝ) + 1)))) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let A : Ω → ℝ≥0∞ := fun ω => NX ω (Ioc 0 s ×ˢ Bp)
    let F : Ω → ℝ≥0∞ := fun ω => NX ω (Ioc s t ×ˢ Bf)
    let rp : ℝ := ((s : ℝ≥0∞) * X.ν Bp).toReal
    let rf : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν Bf).toReal
    Integrable (fun ω => ((A ω).toReal - rp) * ((F ω).toReal - rf)) P ∧
    (∫ ω, ((A ω).toReal - rp) * ((F ω).toReal - rf) ∂P) = 0 := by sorry
