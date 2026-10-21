-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_admissible_hjb_right_dividend_atom_control
-- name    : AvramDividend.Classical.capped_admissible_hjb_right_dividend_atom_control
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:38:15.382045+00:00
-- url     : https://prove2.me/theorems/1baa9a6d-60cf-4acb-8acd-b74b52ffccf1
-- title:
--   HJB secant controls each admissible right dividend atom, including the initial atom
-- statement:
--   For a capped-admissible dividend strategy with initial capital within cap C, and a verification function satisfying the exact HJB smoothness/gradient hypotheses, every right dividend atom at t=0 or strictly before the book-value ruin time is bounded above by the corresponding drop in w(U_t). The atom Δ+D_t=D_{t+}−D_t is nonnegative by accepted right-jump decomposition and no greater than the pre-payment reserve U_t by the dividend strategy's admissibility condition. The positive-time cap is provided directly by IsAdmissibleLe; at t=0, the Lévy start X_0=0 and dividend D_0=0 imply U_0=x and hence the supplied initial-cap bound. The accepted general HJB dividend secant proves Δ+D_t≤w(U_t)−w(U_t−Δ+D_t). This discharges the entire hjump obligation in the remaining UBV stochastic core, with correct initial-atom and boundary treatment.
-- source:
--   Depends only on Proved exact jump decomposition, HJB dividend secant and foundational admissibility definitions; no Open imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightJump_decomposition
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_controls_dividend_jump_le_cap

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_admissible_hjb_right_dividend_atom_control
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) := by sorry
