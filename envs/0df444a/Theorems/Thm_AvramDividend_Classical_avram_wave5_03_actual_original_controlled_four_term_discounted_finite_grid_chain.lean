-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_original_controlled_four_term_discounted_finite_grid_chain
-- name    : AvramDividend.Classical.avram_wave5_03_actual_original_controlled_four_term_discounted_finite_grid_chain
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:12:22.986415+00:00
-- url     : https://prove2.me/theorems/6e9ccb50-e5cb-4098-aae1-fce7ead9acfb
-- title:
--   Exact original controlled Lévy finite-grid discounted four-event chain with initial dividend atom
-- statement:
--   On the actual path of SpectrallyNegativeLevy X and the same adapted dividend control D, any finite monotone clock beginning at zero gives an exact discounted change-of-variables accounting. Each cell has four separate chronological contributions: discount change on previous postpayment reserve, original Lévy source observation with dividends frozen at the preceding right limit, the accumulated prepayment control drop between cells (including diffuse and singular-continuous dividends), and the right-hand lump-sum control drop at the new observation. The genuine time-zero correction w(x-rightLimit D 0)-w(x) is explicit. The source identity X.X_zero=0 determines the initial state. This is a pathwise finite-grid decomposition for BV C1 and UBV C2 limits; it does not claim the stochastic Ito-Meyer continuum limit or replace 04-B's Stieltjes measure control.
-- source:
--   Actual source definitions riskProcess X x D = x+X.X-D, rightLimit D, X.X_zero, admissible source dividend strategy. Connects the 04-B complete Stieltjes source control and 03-A Gaussian/03-B source jump increments to BV ef7e6c20 and corrected UBV 429e17ca via a mesh-to-Ito-Meyer limit still requiring proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_actual_original_controlled_four_term_discounted_finite_grid_chain
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (hzero : u 0 = 0) (n : ℕ) :
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    E (u n) * w (Y (u n)) =
      w x + (w (x - rightLimit D 0 ω) - w x) +
      ∑ i ∈ Finset.range n,
        ((E (u (i + 1)) - E (u i)) * w (Y (u i)) +
          E (u (i + 1)) * (w (Z i) - w (Y (u i))) +
          E (u (i + 1)) *
            (w (riskProcess X x D (u (i + 1)) ω) - w (Z i)) +
          E (u (i + 1)) *
            (w (Y (u (i + 1))) -
              w (riskProcess X x D (u (i + 1)) ω))) := by sorry
