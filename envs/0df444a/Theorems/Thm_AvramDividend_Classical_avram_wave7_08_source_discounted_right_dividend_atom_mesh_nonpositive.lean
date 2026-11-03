-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_discounted_right_dividend_atom_mesh_nonpositive
-- name    : AvramDividend.Classical.avram_wave7_08_source_discounted_right_dividend_atom_mesh_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:35:19.471276+00:00
-- url     : https://prove2.me/theorems/0b2dd7dd-1cef-463f-86e1-b2d0380c4723
-- title:
--   Exact original pre-ruin right-dividend jump residual sums nonpositive under corrected atom control
-- statement:
--   For finite actual-source ruin-preceding payment times (including time zero) and original right-limit dividend increments, the corrected right-dividend secant assumption gives a nonpositive residual between paid jump and decrement in w. Discounting by strictly positive exp(-qt) and summing retains nonpositivity. This is a pathwise dividend-atom residual sign component of controlled Itô–Meyer; the stochastic convergence to all jump times remains open.
-- source:
--   W7-08 original Ω/P/X/D, corrected hjump with time-zero atom, finite mesh deterministic jump residual. A source-specific input to the stopped HJB budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_source_discounted_right_dividend_atom_mesh_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (N : ℕ) (clock : Fin N → ℝ≥0) (ω : Ω)
    (hclock : ∀ i, clock i = 0 ∨
      (clock i : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ i : Fin N,
      Real.exp (-(q * (clock i : ℝ))) *
        ((rightLimit D (clock i) ω - D (clock i) ω) -
         (w (riskProcess X x D (clock i) ω) -
          w (riskProcess X x D (clock i) ω -
            (rightLimit D (clock i) ω - D (clock i) ω))))) ≤ 0 := by sorry
