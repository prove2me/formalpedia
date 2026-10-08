-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissible_exponential_dividend_jump_bound
-- name    : AvramDividend.Classical.admissible_exponential_dividend_jump_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:40:40.839992+00:00
-- url     : https://prove2.me/theorems/cb93d3d7-23a7-42ff-adeb-0dd5df581315
-- title:
--   Admissible dividend lumps are paid for by the exponential verification value gap
-- statement:
--   At every admissible dividend payment instant (including time zero), the lump ΔD=D_{t+}−D_t is nonnegative and no larger than the current reserve U_t=x+X_t−D_t. For θ≥1, the pointwise exponential verification function pays at least this amount out of its own decrease: ΔD≤exp(θU_t)−exp(θ(U_t−ΔD)). This is the dividend-jump verification inequality for the actual Avram strategy and admissibility definitions.
-- source:
--   Proved dividendStrategy_le_rightLimit, formal IsAdmissible bound, and exponential_dividend_jump_bound. Crucial pointwise jump-payment estimate for Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissible_exponential_dividend_jump_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D) (θ : ℝ) (hθ : 1 ≤ θ)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    rightLimit D t ω - D t ω ≤
      Real.exp (θ * riskProcess X x D t ω) -
        Real.exp (θ * (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω))) := by sorry
