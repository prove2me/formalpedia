-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_04_positive_horizon_strict_survival_terminal_max_eq_signed
-- name    : AvramDividend.Classical.avram_wave8_04_positive_horizon_strict_survival_terminal_max_eq_signed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:12:18.854349+00:00
-- url     : https://prove2.me/theorems/bf5bcf26-078c-4dc3-856a-cd5aefb9190c
-- title:
--   Original BV positive-horizon strict-survival terminal max equals signed stopped candidate
-- statement:
--   For every positive deterministic horizon and path strictly surviving the original ruin time, the capped postrightpayment reserve lies in [0,C]. The full-cap gradient secant and nonnegative boundary value imply w(postreserve)>=0. Thus the exact discounted terminal max 0 coincides pointwise with the signed terminal used in the stopped generator identity. Preserves all original X,P,filtration,D and rightLimit, including survival test.
-- source:
--   Original-source Proposition 4(i) stopped terminal, exact positive-cap BV supplementary identity, child of W8-04 positive-horizon scalar budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_04_positive_horizon_strict_survival_terminal_max_eq_signed
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T,hT⟩
    ∀ ω,
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω))
       else 0) =
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
       else 0) := by sorry
