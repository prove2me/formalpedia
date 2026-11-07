-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_intrinsic_weighted_negative_mark_mass_finite
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_intrinsic_weighted_negative_mark_mass_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T19:01:43.812128+00:00
-- url     : https://prove2.me/theorems/0c16cc08-3089-4639-add9-bc7ffbe600e6
-- title:
--   Original BV intrinsic Lévy negative-jump magnitude remains finite after compact C1 envelope scaling
-- statement:
--   On the exact actual original BV Lévy half-open (0,T] jump measure, every fixed nonnegative compact-band C1 coefficient C preserves integrability of the negative mark magnitude. This imports the proved unweighted finite mass and applies the pinned Mathlib lintegral constant-multiplication identity, directly supporting the original stopped H jump-envelope domination certificate.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_intrinsic_negative_mark_mass_finite_on_clock

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_intrinsic_weighted_negative_mark_mass_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (C : ℝ), 0 ≤ C →
      let Δ : ℝ≥0 → ℝ := fun u =>
        X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u
      let NT : Measure (ℝ≥0 × ℝ) :=
        ((Measure.count.restrict
          ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} ∩ Ioc 0 T)).map
            (fun u : ℝ≥0 => (u, Δ u)))
      (∫⁻ p, ENNReal.ofReal (C * (-p.2)) ∂NT) < ⊤ := by sorry
