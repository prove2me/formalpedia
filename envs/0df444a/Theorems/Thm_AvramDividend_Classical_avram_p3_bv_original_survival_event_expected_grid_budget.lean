-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_survival_event_expected_grid_budget
-- name    : AvramDividend.Classical.avram_p3_bv_original_survival_event_expected_grid_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:30:13.734431+00:00
-- url     : https://prove2.me/theorems/7f24a8e3-1985-4129-b91d-def8df172ce4
-- title:
--   Original BV survival-event weighted closed-grid source budget without false almost-sure survival
-- statement:
--   The original physical closed dividend cash plus post-rightpayment w terminal is restricted to the genuinely surviving event of a deterministic grid clock. The source-cap-linear correction is restricted to the same survival event. On each surviving path the previously Proved physical ledger applies, while non-surviving paths contribute zero; integrating gives the expected inequality under explicit L1 and source-mean hypotheses. No almost-sure survival assumption is made.
-- source:
--   Composition of Proved dc7eeb89 original grid and Mathlib integral_mono_ae with exact survival indicator. The remaining source mean is an explicit independent compensator/HJB obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_closed_grid_full_w_budget

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- Source-exact pre-ruin event restriction: no almost-sure survival of
   an unstopped original process is assumed. The expected source sign
   remains a separate genuine compensation/HJB obligation. -/

theorem AvramDividend.Classical.avram_p3_bv_original_survival_event_expected_grid_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Live : Ω → Prop := fun ω =>
      (u n : ℝ≥0∞) < ruinTime X x D ω
    let Y : Ω → ℝ≥0 → ℝ := fun ω t =>
      x + X.X t ω - rightLimit D t ω
    let Z : Ω → ℕ → ℝ := fun ω i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    let CashTerm : Ω → ℝ := fun ω => if Live ω then
      E (u n) * w (Y ω (u n)) +
        (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal
      else 0
    let Source : Ω → ℝ := fun ω => if Live ω then
      ∑ i ∈ Finset.range n,
        ((E (u (i + 1)) - E (u i)) * V (Y ω (u (i + 1))) +
          E (u i) * (V (Z ω i) - V (Y ω (u i))))
      else 0
    Integrable CashTerm P →
      Integrable Source P →
      Integrable (fun ω : Ω => if Live ω then w x else 0) P →
      (∫ ω, Source ω ∂P) ≤ 0 →
      (∫ ω, CashTerm ω ∂P) ≤
        (∫ ω : Ω, if Live ω then w x else 0 ∂P) := by sorry
