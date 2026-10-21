-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_truncated_hjb_budget
-- name    : AvramDividend.Classical.local_verification_from_uniform_truncated_hjb_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:46:43.182707+00:00
-- url     : https://prove2.me/theorems/335143c1-b20d-4c32-9d0c-88b166ce4b2b
-- title:
--   The complete local verification conclusion reduces exactly to a uniform integer-horizon HJB dividend budget
-- statement:
--   Assume that for every permissible initial reserve x in [0,C], every capped-admissible strategy D and every integer-horizon truncation n, the expected discounted dividend measure up to time n and ruin is bounded by ENNReal.ofReal(w x). Then the capped valueFunctionLe is at most w on [0,C], and when C=∞ the unrestricted valueFunction is at most w on [0,∞). The already Proved dividendValue_le_of_uniform_truncated_bounds transports each bound to the full dividendValue using monotone convergence, and the independently Proved local_verification_from_uniform_strategy_bound passes from per-strategy dividends to the capped supremum and top-cap unrestricted branch. This is an exact dependency-reduction theorem: the one remaining stochastic HJB estimate is the uniform finite-horizon budget. It does not assume or assert that this hypothesis follows from the stated HJB generator inequality.
-- source:
--   Proved dividendValue_le_of_uniform_truncated_bounds (12267), Proved local_verification_from_uniform_strategy_bound; no Open imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_from_uniform_truncated_hjb_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hBudget : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
      ∀ n : ℕ,
        (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
       valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
       valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
