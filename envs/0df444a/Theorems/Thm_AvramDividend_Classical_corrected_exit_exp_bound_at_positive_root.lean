-- Prove2me | Theorems.Thm_AvramDividend_Classical_corrected_exit_exp_bound_at_positive_root
-- name    : AvramDividend.Classical.corrected_exit_exp_bound_at_positive_root
-- status  : Open
-- author  : @WillR
-- created : 2026-10-22T22:53:29.696685+00:00
-- url     : https://prove2.me/theorems/a6c37169-463b-4d4e-8389-b558ade5b960
-- title:
--   Stopped exponential q-discounted upper-first exit bound at the prescribed positive Esscher root
-- statement:
--   For a spectrally negative Lévy process with no positive jumps, positive q and φ>0 satisfying ψ(φ)=q, the native corrected upward-before-ruin q-discounted exit expectation from reserve x below barrier a is bounded above by exp(-φ(a-x)). Derive via the positive exponential martingale exp(φ X_t−qt), bounded grid optional stopping, no-upper-overshoot, and Fatou/time-grid convergence; no Standing or Gaussian assumption. The pure stopped-exponential integration inequality is already Proved on Prove2Me as discounted_upper_exit_of_stopped_exponential. Do not assume the scale-function exit ratio or circular Esscher monotonicity.
-- source:
--   Optional sampling of spectrally negative Lévy exponential martingale; Prove2Me levy_grid_upper_exit_discount_bound_complete and discounted_upper_exit_of_stopped_exponential.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.corrected_exit_exp_bound_at_positive_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) (hxa : x ≤ a) :
    twoSidedExitExpectationCorrected X q a x ≤
      ENNReal.ofReal (Real.exp (-(φ * (a - x)))) := by sorry
