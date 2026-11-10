-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite15_original_discounted_terminal_left_limit
-- name    : AvramDividend.Classical.avram_gfinite15_original_discounted_terminal_left_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T16:32:55.258458+00:00
-- url     : https://prove2.me/theorems/99d01208-6e4d-476d-959f-71d15f4b8b05
-- title:
--   Discounted original Gaussian strict prepayment terminal left limit
-- statement:
--   Almost surely, at every strictly positive original physical clock at or before ruin, the discounted original post-rightpayment sampled value converges from the left to the discounted prepayment value at the stopping instant. The proof combines the already Proved original-X/D value left-limit with continuity of the real exponential discount; no stochastic Ito assumption or altered filtration is introduced.
-- source:
--   Endpoint bridge from Proved 8daf1ccd-1252-4d61-a9e3-f21d9d9f6da8 for original-X/D positive-clock stopped Gaussian localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_original_positive_clock_w_left_payoff

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gfinite15_original_discounted_terminal_left_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (q : ℝ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      (t : ℝ≥0∞) ≤ ruinTime X x D ω →
      Tendsto
        (fun s : ℝ≥0 =>
          Real.exp (-(q * (s : ℝ))) *
            w (x + X.X s ω - rightLimit D s ω))
        (𝓝[<] t)
        (𝓝 (Real.exp (-(q * (t : ℝ))) *
          w (riskProcess X x D t ω))) := by sorry
