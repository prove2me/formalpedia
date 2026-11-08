-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_finite_row_clipping_eventually_exact
-- name    : AvramDividend.Classical.avram_bv_residual10_original_finite_row_clipping_eventually_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:36:23.389437+00:00
-- url     : https://prove2.me/theorems/407524db-7a25-4c23-87fc-90692999d18f
-- title:
--   Fixed original Levy physical row eventually equals every sufficiently high coefficient clipping
-- statement:
--   For any fixed sample path and fixed finite physical mesh of the original spectrally negative Levy process, the exact raw residual weighted finite sum equals the coefficient-clipped sum for all sufficiently large integer clipping levels. This is a finite-set Archimedean fact preserving the original real raw jump-time tsum, deterministic grid and same-path increments. It enables a later Fatou or localisation proof to take a pointwise limit of genuinely L1 clipped approximants while keeping uniform-integrability as a separate obligation.
-- source:
--   AVRAM BV-RESIDUAL10 exact finite-row original coefficient unclipping, 7 November 2026

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_finite_row_clipping_eventually_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ) (a : Ω → ℕ → ℝ) (ω : Ω) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) - J t
    ∃ N : ℕ, ∀ k ≥ N,
      (∑ i ∈ Finset.range (n + 1),
        (if |a ω i| ≤ (k : ℝ) then a ω i else 0) *
          (R (u n i) - R (u n (i + 1)))) =
      (∑ i ∈ Finset.range (n + 1),
        a ω i * (R (u n i) - R (u n (i + 1)))) := by sorry
