-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_positive_root_unrestricted_upcrossing_discount_bound
-- name    : AvramDividend.Classical.levy_positive_root_unrestricted_upcrossing_discount_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-22T23:02:00.465986+00:00
-- url     : https://prove2.me/theorems/eb6bd8bb-0632-4518-bc3e-590a6d258e8b
-- title:
--   One-sided first-upcrossing q-discounted exponential bound at positive Esscher root, without Standing
-- statement:
--   For any spectrally negative Lévy process whose Laplace exponent has φ>0 with ψ(φ)=q>0, and any z≥0, the expected q-discount factor for first strict upcrossing of level z (zero if the time is infinite) is at most exp(−φ z). This is the unrestricted one-sided exponential-martingale first-passage bound, requiring no Standing condition, no Gaussian coefficient, no bounded-variation hypothesis and no scale-function identity. Prove by bounded optional sampling of the nonnegative martingale exp(φ X_t−qt), pathwise upper first-passage overshoot control from noPosJumps, and Fatou convergence from finite uniform grids. The general moment inequality discounted_upper_exit_of_stopped_exponential is Proved; the finite grid lemma levy_grid_upper_exit_discount_bound_complete and mesh-limit lemma chat03_actual_upperfirst_grid_discount_tendsto are Proved. This theorem is the precise remaining stochastic core of the independent corrected_exit_exp_bound_at_positive_root leaf.
-- source:
--   First-passage exponential martingale; Avram et al 2007; Prove2Me finite-grid upper exit and stopping lemmas.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_positive_root_unrestricted_upcrossing_discount_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 ≤ z) :
    (∫⁻ ω, if twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)
       then ENNReal.ofReal
         (Real.exp (-(q * ENNReal.toReal
           (twoSidedExitUpTimeCorrected X z ω))))
       else 0 ∂P) ≤ ENNReal.ofReal (Real.exp (-(φ * z))) := by sorry
