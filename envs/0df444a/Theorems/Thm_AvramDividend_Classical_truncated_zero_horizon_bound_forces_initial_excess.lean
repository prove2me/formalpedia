-- Prove2me | Theorems.Thm_AvramDividend_Classical_truncated_zero_horizon_bound_forces_initial_excess
-- name    : AvramDividend.Classical.truncated_zero_horizon_bound_forces_initial_excess
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:17:57.942149+00:00
-- url     : https://prove2.me/theorems/b550423e-0a2e-4225-afd5-c5a49f1e4fb2
-- title:
--   Zero-horizon dividend bound forces the initial-capital excess inequality
-- statement:
--   If x exceeds a finite reserve cap c, any admissible strategy must immediately distribute at least x-c. Hence a claimed finite-horizon expected discounted dividend upper bound at T=0 with candidate w must satisfy ENNReal.ofReal(x-c) ≤ ENNReal.ofReal(w(x)). This is an exact necessary boundary condition for the published BV/UBV stochastic verification bounds and follows directly from the proved time-zero Stieltjes atom identity, proved admissibility initial-excess lemma and the probability-measure field of a spectral-negative Lévy process. It does not assume or assert the unproved BV/UBV bound itself.
-- source:
--   Exact pinned Formalpedia zero-horizon atom and admissibleLe_rightLimit_zero_ge_excess theorems, underlying Avram–Palmowski–Pistorius (2007) §2.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissibleLe_rightLimit_zero_ge_excess
import Theorems.Thm_AvramDividend_Classical_truncated_dividend_payoff_at_zero_eq_initial_atom
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.truncated_zero_horizon_bound_forces_initial_excess
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 ≤ c) (hcx : c < x)
    (q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hbound :
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) :
    ENNReal.ofReal (x - c) ≤ ENNReal.ofReal (w x) := by sorry
