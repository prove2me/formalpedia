-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_monotone_R_mesh_bound
-- name    : AvramDividend.Classical.avram_bv_residual10_original_monotone_R_mesh_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:30:00.384405+00:00
-- url     : https://prove2.me/theorems/b5f11d6e-a1a4-4167-9676-ec609cb0a5c6
-- title:
--   Original BV monotone residual weighted physical mesh bounded by endpoint growth
-- statement:
--   For an original BV Lévy sample path whose exact raw negative-jump drift remainder is monotone, any monotone physical mesh and any weights bounded in absolute value by K satisfy the sharp pathwise bound of the weighted residual increment sum by K times the remainder's net endpoint growth. This combines the Proved original-process weighted-variation lemma with telescoping of a monotone function along the finite mesh. The separate proved almost-sure raw remainder monotonicity provides the hRmono hypothesis, and compact reserve localisation provides hK for the exact stopped discounted derivative weights.
-- source:
--   AVRAM BV-RESIDUAL10 original-process pathwise mesh bound; Proved ce2d2c97 and pinned Finset.sum_range_sub, 7 November 2026

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_weighted_R_variation_bound
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_monotone_R_mesh_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (hRmono : Monotone (fun t : ℝ≥0 =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)))
    (a : ℕ → ℝ) (K : ℝ)
    (hK : ∀ i ∈ Finset.range (n + 1), |a i| ≤ K) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) - J t
    |∑ i ∈ Finset.range (n + 1),
      a i * (R (u n i) - R (u n (i + 1)))| ≤
        K * (R (u n (n + 1)) - R (u n 0)) := by sorry
