-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_prepayment_terminal_L1
-- name    : AvramDividend.Classical.avram_ubv_finite13_original_stopped_prepayment_terminal_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:32:47.917974+00:00
-- url     : https://prove2.me/theorems/7f672fd4-63ca-4e71-ba54-e1f5a6d328d8
-- title:
--   Original finite-cap bounded discounted prepayment terminal is integrable at every physical stopping clock
-- statement:
--   For an original finite-cap admissible dividend strategy and any genuine right-continuous stopped clock, the discounted payoff evaluated at the original prepayment reserve is L1. The actual reserve is capped, w is continuous on the nonnegative compact cap interval and zero on negative reserves, so its absolute value is uniformly bounded. Original prepayment risk is jointly measurable; the clock is measurable; nonnegative discount makes exp(-q sigma) at most one. No auxiliary process, Brownian extraction, or bounded clock assumption.
-- source:
--   Direct supporting obligation for the selected original strict Gaussian child d1caa4aa; combines with Proved ed1a42d8 strict cash L1 before centering the strict reward.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite13_original_stopped_prepayment_terminal_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    Integrable (fun ω =>
      Real.exp (-(q * (σ ω : ℝ))) *
        w (riskProcess X x D (σ ω) ω)) P := by sorry
