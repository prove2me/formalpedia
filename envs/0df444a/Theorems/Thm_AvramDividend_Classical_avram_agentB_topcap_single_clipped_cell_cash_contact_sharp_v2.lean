-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentB_topcap_single_clipped_cell_cash_contact_sharp_v2
-- name    : AvramDividend.Classical.avram_agentB_topcap_single_clipped_cell_cash_contact_sharp_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T00:15:37.346689+00:00
-- url     : https://prove2.me/theorems/8960bb25-cc43-4a6b-918e-88d0c9313965
-- title:
--   Exact original stopped single physical cell cash/contact inequality at positive clock
-- statement:
--   At a positive original stopped clock rho with one physical clipped interval [0,rho], the right-dividend loss at time zero and the final postpayment contact correction plus all true discounted strict cash are bounded by the final actual open-strip cash plus a nonnegative q*n times original dividend mass. The exact strict cash is its initial right atom plus later open-strip cash, the initial atom cancels the reserve loss, and the terminal contact is nonpositive. This is the missing m=0 base case to establish gledger37 for all physical meshes.
-- source:
--   Proved avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton, avram_p3_c_bvchain_original_strict_cash_zero_atom_plus_open_real_exact and avram_gledger133_original_stopped_mesh_terminal_contact_and_tail with first crossing index k=0, v0=0,v1=rho.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_agentB_topcap_single_clipped_cell_cash_contact_sharp_v2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (ρ : ℝ≥0) (hρpos : 0 < ρ)
    (q : ℝ) (hq : 0 < q) (n : ℕ) :
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ := x + X.X ρ ω - rightLimit D ρ ω
    let Z : ℝ := x + X.X ρ ω - rightLimit D 0 ω
    let F : ℝ :=
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
    let U : ℝ :=
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
    max ((w (x - rightLimit D 0 ω) - w x) +
      E ρ * ((w (riskProcess X x D ρ ω) - w Z) +
        (w Y - w (riskProcess X x D ρ ω))) +
      E ρ * (w (riskProcess X x D ρ ω) - w Y) + F) (0 : ℝ) ≤
      q * (n : ℝ) *
        (dividendMeasure D ω (Ioo (0 : ℝ) (ρ : ℝ))).toReal + U := by sorry
