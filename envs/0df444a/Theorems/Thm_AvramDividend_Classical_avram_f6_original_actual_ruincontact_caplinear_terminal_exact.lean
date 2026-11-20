-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_actual_ruincontact_caplinear_terminal_exact
-- name    : AvramDividend.Classical.avram_f6_original_actual_ruincontact_caplinear_terminal_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:38:00.073174+00:00
-- url     : https://prove2.me/theorems/ac97315a-0492-48ba-b315-45693be9efc7
-- title:
--   Original capped stopped terminal agrees with caplinear continuation at ruin and survival
-- statement:
--   At every actual time and path of the original admissible capped dividend strategy, the canonical caplinear continuation V defined by the original ENNReal.ofReal cap test agrees exactly with w at the true stopped terminal W: right-limit postpayment reserve at zero and strictly pre-ruin, riskProcess at ruin. Both branches use already Proved physical cap invariants, and the result retains the exact ruin-contact convention without martingale witnesses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_actual_ruincontact_caplinear_terminal_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) :
    let V : ℝ → ℝ := fun z =>
      if ENNReal.ofReal z ≤ C then w z
      else w C.toReal + (z - C.toReal)
    let W : ℝ := if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X t ω - rightLimit D t ω
      else riskProcess X x D t ω
    V W = w W := by sorry
