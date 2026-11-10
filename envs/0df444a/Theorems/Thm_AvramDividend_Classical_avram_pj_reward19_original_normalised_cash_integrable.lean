-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward19_original_normalised_cash_integrable
-- name    : AvramDividend.Classical.avram_pj_reward19_original_normalised_cash_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:44:05.927293+00:00
-- url     : https://prove2.me/theorems/43ca79c2-62ba-4fbd-a58c-182b6ac3785d
-- title:
--   Original discounted closed stopped dividend cash is integrable when the zero-normalised reward is integrable
-- statement:
--   For the true original unbounded-variation controlled process and any original right-continuous finite stopping clock, the target zero-normalised discounted stopped reward dominates its own nonnegative closed discounted dividend cash. The branch at clock zero uses the exact admissible initial payment inequality, while the terminal function is nonnegative by the gradient lower envelope. Consequently integrability of the target normalised reward forces integrability of its genuine stopped cash, with no separate cash-L1 assumption. This is a necessary input to the original pure-jump stopped verification 8d851948 and the existing upcross/Fatou reductions.
-- source:
--   Compose source-exact Proved ef1ac2df zero-mask reward domination, f6fef241 nonnegative terminal, and d0eb0e63 original-clock cash measurability, then use dominated integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_masked_reward_dominates_exact_F
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopped_real_cash_measurable_no_aux
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward19_original_normalised_cash_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) :
    let Cash : Ω → ℝ := fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    let G : Ω → ℝ := fun ω =>
      if ρ ω = 0 then w x else
        Real.exp (-(q * (ρ ω : ℝ))) *
          w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
            else riskProcess X x D (ρ ω) ω) + Cash ω
    Integrable G P → Integrable Cash P := by sorry
