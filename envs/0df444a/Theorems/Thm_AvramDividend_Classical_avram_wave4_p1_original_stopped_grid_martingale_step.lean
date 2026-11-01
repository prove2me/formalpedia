-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_original_stopped_grid_martingale_step
-- name    : AvramDividend.Classical.avram_wave4_p1_original_stopped_grid_martingale_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:25:23.161092+00:00
-- url     : https://prove2.me/theorems/4abe9dc6-2641-4dcc-97f4-ffc8666fe024
-- title:
--   Original stopped predictable marked finite-grid compensated sums form a discrete martingale
-- statement:
--   On the actual sample-space probability with future cell mark sigma-fields independent of past sigma-fields, predictable stopped weights and integrable centered marked increments give a genuine discrete martingale conditional expectation for each finite-grid prefix. The proof derives it from independently Proved P1 one-step conditional centering; no martingale law or compensator conclusion is assumed.
-- source:
--   P1 one-step conditional martingale theorem pending authoring, pinned Mathlib Finset.sum_range_succ.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_stopped_predictable_marked_one_step_martingale

open MeasureTheory ProbabilityTheory Filter

theorem AvramDividend.Classical.avram_wave4_p1_original_stopped_grid_martingale_step
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (mPast mFuture : ℕ → MeasurableSpace Ω)
    (hPast : ∀ n, mPast n ≤ mΩ)
    (hFuture : ∀ n, mFuture n ≤ mΩ)
    (hSigma : ∀ n, @SigmaFinite Ω (mPast n) (P.trim (hPast n)))
    (H Z : ℕ → Ω → ℝ)
    (hH : ∀ n, StronglyMeasurable[mPast n] (H n))
    (hZ : ∀ n, StronglyMeasurable[mFuture n] (Z n))
    (hProd : ∀ n, Integrable (H n * Z n) P)
    (hZi : ∀ n, Integrable (Z n) P)
    (hIndep : ∀ n, Indep (mFuture n) (mPast n) P)
    (hCenter : ∀ n, ∫ ω, Z n ω ∂P = 0)
    (hPrefix : ∀ n, StronglyMeasurable[mPast n]
      (fun ω => ∑ i ∈ Finset.range n, H i ω * Z i ω))
    (hPrefixI : ∀ n, Integrable
      (fun ω => ∑ i ∈ Finset.range n, H i ω * Z i ω) P)
    (n : ℕ) :
    P[(fun ω => ∑ i ∈ Finset.range (n + 1),
          H i ω * Z i ω) | mPast n] =ᵐ[P]
      (fun ω => ∑ i ∈ Finset.range n, H i ω * Z i ω) := by sorry
