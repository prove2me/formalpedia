-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_admissible_bookReserve_candidate_nonnegative_preRuin
-- name    : AvramDividend.Classical.capped_admissible_bookReserve_candidate_nonnegative_preRuin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:36:27.479647+00:00
-- url     : https://prove2.me/theorems/cd9655ac-edda-49b9-a69e-afe57d8a5f01
-- title:
--   HJB candidate is nonnegative on the actual pre-ruin book-value reserve of a capped strategy
-- statement:
--   At each positive time strictly before the exact book-value ruinTime of a capped-admissible dividend strategy, w(riskProcess X x D t ω) is nonnegative under the root local verification HJB gradient and continuity hypotheses. Proved pre-ruin solvency gives 0≤Uplus=x+X_t−D_{t+}. Proved exact right-dividend jump decomposition gives Uplus≤U=x+X_t−D_t. Hence U≥0, while the positive-time cap field of IsAdmissibleLe gives ENNReal.ofReal(U)≤C. The independently accepted HJB lower bound w(U)≥U+w(0)≥0 applies, discharging the explicit hw_nonneg hypothesis of the remaining unbounded-variation stochastic core without any extra stochastic Ito assumption.
-- source:
--   Exact Proved pre-ruin solvency, right-jump accounting, capped-admissible positive-time bound and HJB candidate lower bound; no Open imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightJump_decomposition
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_candidate_lower_bound_on_cap

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_admissible_bookReserve_candidate_nonnegative_preRuin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω) := by sorry
