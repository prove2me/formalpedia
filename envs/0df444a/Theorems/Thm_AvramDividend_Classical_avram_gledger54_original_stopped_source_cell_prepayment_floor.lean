-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger54_original_stopped_source_cell_prepayment_floor
-- name    : AvramDividend.Classical.avram_gledger54_original_stopped_source_cell_prepayment_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T23:22:57.892503+00:00
-- url     : https://prove2.me/theorems/929f0926-364a-457f-87be-211abece9180
-- title:
--   Original stopped Gaussian physical source cells retain the positive prepayment reserve floor
-- statement:
--   For every active physical stopped Gaussian mesh cell, the reserve BEFORE payment at its clipped right endpoint is bounded below by the same strictly positive compact-prefix floor. The endpoint may equal the random stop rho. Use Proved original zero-jump stopped terminal prepayment band d81c6b24 for that case; otherwise use the strict interior prefix. The right-limit dividend at the left grid time is no larger than the actual dividend process at the later clipped endpoint, directly from the infimum definition of rightLimit. Handles initial right payment and last-cell stopping without an auxiliary process.
-- source:
--   Necessary physical endpoint fact for new gledger53 original clipped source positive-part integrability; keeps source argument Z_i above the compact positive anchor so one-sided HJB exponential upper growth controls w(Z_i). Reuses Proved d81c6b24 zero-jump stop prepayment floor.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger54_original_stopped_source_cell_prepayment_floor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (j n m : ℕ) (hn : 0 < n)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ᵐ ω ∂P, ∀ i ∈ Finset.range (m + 1),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let v : ℝ≥0 := min (((i + 1 : ℕ) : ℝ≥0) * Δ) (ρ ω)
      s < ρ ω →
        (1 : ℝ) / ((j : ℝ) + 1) ≤
          x + X.X v ω - rightLimit D s ω := by sorry
