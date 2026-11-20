-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_trueclip_original_discount_cash_abs_mesh_eventual
-- name    : AvramDividend.Classical.avram_pj_workerC_trueclip_original_discount_cash_abs_mesh_eventual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:02:17.106288+00:00
-- url     : https://prove2.me/theorems/483ba6d9-cd41-41f5-9ccb-427fa694105d
-- title:
--   True ruin-clipped subordinate clock has vanishing L1 physical discount cash mesh error
-- statement:
--   For the actual original post-right dividend measure and natural ruin-clipped horizon τ, any stopping clock ρ≤τ has cash mesh discrepancy E_m built from the original positive-time dividendMeasure, true paymentTimes and discounted final subinterval. For every ε>0, all sufficiently fine physical grids have Integrable E_m with absolute expected error ≤ ε. All clock bounds follow from existing Proved original clipping certificates.
-- source:
--   Proved original bounded stopped discount cash absolute L1 0c5ef385 and Proved subordinate clock true horizon and ruin bound edebe535.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_bounded_stopped_discount_cash_mesh_absolute_error_L1_eventual
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_trueclip_original_discount_cash_abs_mesh_eventual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (n : ℕ) (hn : 0 < n)
    (τ ρ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) :
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let u : ℝ≥0 := ρ ω - Δ
      q * (Δ : ℝ) *
        (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo (u : ℝ) (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (E m) P ∧ (∫ ω, |E m ω| ∂P) ≤ ε := by sorry
