-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_postPayment_candidate_uniform_upper_bound_finite_cap
-- name    : AvramDividend.Classical.capped_postPayment_candidate_uniform_upper_bound_finite_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:35:36.704453+00:00
-- url     : https://prove2.me/theorems/f7029cc5-793e-418f-9446-2904e497f1b5
-- title:
--   Finite-cap post-payment candidate values admit a uniform deterministic upper bound
-- statement:
--   Fix a finite real cap c≥0, initial capital satisfying ofReal x≤ofReal c, an admissible capped dividend strategy and a candidate w continuous on nonnegative reals and identically zero on negative reals. There exists a deterministic B≥0 such that w(x+X_t(ω)−D_{t+}(ω))≤B for all paths ω and all times t. The Proved all-times capped post-payment bound ensures ofReal of the post-payment reserve≤ofReal c. For nonnegative reserve, the exact pinned ENNReal.ofReal_le_ofReal_iff yields reserve≤c. Compactness of [0,c] and ContinuousOn w give an upper bound M for w on this interval by the pinned IsCompact.bddAbove_image. For negative reserve w=0. Thus max(0,M) is a deterministic upper bound, independent of time and outcome. The theorem does not claim integrability of stochastic integrals or a stopped martingale formula.
-- source:
--   Source-faithful consequence of accepted capped_postPaymentReserve_ofReal_le_cap plus pinned ENNReal.ofReal_le_ofReal_iff and IsCompact.bddAbove_image; no Open dependencies.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_postPayment_candidate_uniform_upper_bound_finite_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 ≤ c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ω : Ω) (t : ℝ≥0),
      w (x + X.X t ω - rightLimit D t ω) ≤ B := by sorry
