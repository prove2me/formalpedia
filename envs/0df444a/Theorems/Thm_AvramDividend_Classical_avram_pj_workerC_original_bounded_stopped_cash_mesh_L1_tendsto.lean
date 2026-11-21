-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_bounded_stopped_cash_mesh_L1_tendsto
-- name    : AvramDividend.Classical.avram_pj_workerC_original_bounded_stopped_cash_mesh_L1_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:02:03.884303+00:00
-- url     : https://prove2.me/theorems/db46101d-84f3-4e1f-8ad4-75feb454bf3d
-- title:
--   Original bounded stopped discounted strict right-dividend cash physical-grid error converges in L1 to zero
-- statement:
--   For the original admissible dividend strategy stopped no later than ruin and a fixed finite horizon, the discounted strict cash discrepancy of the genuine clipped physical mesh tends to zero in L1 as the grid refines; follows from the genuine nonnegative eventually arbitrarily small absolute-mean error estimate.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_bounded_stopped_discount_cash_mesh_absolute_error_L1_eventual
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_bounded_stopped_cash_mesh_L1_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω) :
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let u : ℝ≥0 := ρ ω - Δ
      q * (Δ : ℝ) *
        (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo (u : ℝ) (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
    Tendsto (fun m : ℕ => ∫ ω, |E m ω| ∂P)
      Filter.atTop (𝓝 (0 : ℝ)) := by sorry
