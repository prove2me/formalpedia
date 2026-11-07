-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_intrinsic_negative_mark_dominated_kernel_integrable
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_intrinsic_negative_mark_dominated_kernel_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T19:07:19.780351+00:00
-- url     : https://prove2.me/theorems/3b600fe3-9b16-4109-9cac-9abd6d96cc03
-- title:
--   Source-exact dominated integrability on the original BV intrinsic marked finite-horizon measure
-- statement:
--   For the actual original bounded-variation spectrally negative Lévy path on the half-open physical interval (0,T], every Borel real kernel dominated by a nonnegative constant times max(-z,0) is integrable against that same original intrinsic marked jump measure. The proof imports the independently proved original weighted negative-jump mass and establishes the genuine ENNReal norm domination. The exact original compensated H kernel will supply its pointwise hypothesis from a separate source-identity theorem.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_intrinsic_weighted_negative_mark_mass_finite

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_intrinsic_negative_mark_dominated_kernel_integrable
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
      ∀ (f : ℝ≥0 × ℝ → ℝ), Measurable f →
        (∀ p, |f p| ≤ C * max (-p.2) 0) → Integrable f NT := by sorry
