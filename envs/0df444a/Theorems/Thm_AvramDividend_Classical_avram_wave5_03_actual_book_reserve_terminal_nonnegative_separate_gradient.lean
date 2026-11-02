-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_book_reserve_terminal_nonnegative_separate_gradient
-- name    : AvramDividend.Classical.avram_wave5_03_actual_book_reserve_terminal_nonnegative_separate_gradient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:54:23.498292+00:00
-- url     : https://prove2.me/theorems/52dd2155-e86a-43fe-bb2e-6f91b3bc9e6f
-- title:
--   Original controlled prepayment terminal candidate stays nonnegative at finite ruin and all other sample times under separate BV/UBV gradients
-- statement:
--   For the same original spectrally negative Levy path and the actual capped admissible left-continuous dividend process, the verification function evaluated at the source pre-right-payment riskProcess is nonnegative at EVERY sample time, including the deterministic horizon, exact positive ruin time and initial time. Under the separate interior w'≥1 hypothesis and BV C1 / UBV C2 smoothness, with 0≤w(0), continuity up to zero and w(y)=0 for negative y, admissibility supplies ofReal(riskProcess)≤C at positive times and the initial cap plus X0=D0=0 at zero. At nonnegative reserves the full-cap secant with a=0 gives w(y)≥y+w(0)≥0; for negative overshoots the zero extension applies. No global w≥0, full HJB maximum identity, stopped Ito formula, false assertion that the reserve at ruin is strictly negative, or stochastic compensation is assumed. The theorem is the terminal book reserve complement to BV/UBV postpayment terminal lemmas and can be evaluated at θ=T∧ruinTime pathwise.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), stopped terminal verification term in (5.13). Exact source chronology: book riskProcess before a right payment at positive ruin. Both canonical BV ef7e6c20 and corrected UBV 429e17ca need this terminal boundary condition after their stopped source chain.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_actual_book_reserve_terminal_nonnegative_separate_gradient
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) :
    0 ≤ w (riskProcess X x D t ω) := by sorry
