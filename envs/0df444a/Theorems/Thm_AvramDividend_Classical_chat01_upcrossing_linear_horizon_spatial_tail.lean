-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_upcrossing_linear_horizon_spatial_tail
-- name    : AvramDividend.Classical.chat01_upcrossing_linear_horizon_spatial_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:35:59.819162+00:00
-- url     : https://prove2.me/theorems/466ba72d-7644-4ab2-9785-4e2b3a604308
-- title:
--   Exponential spatial tail for first upcrossing under a linear observation horizon
-- statement:
--   For a finite-horizon measurable upcrossing event, the Esscher Chernoff estimate P(A) ≤ exp(qt−φz) improves to P(A) ≤ exp(−φz/2) whenever twice the time exponent qt is at most the spatial exponent φz. This isolates a quantitative uniform-tail bound for truncation and approximation of killed first-passage events.
-- source:
--   Immediate consequence of the Proved chat01_finite_horizon_upcrossing_probability_explicit_tail and monotonicity of the exponential; Avram, Palmowski and Pistorius (2007), first-passage bounds.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_chat01_finite_horizon_upcrossing_probability_explicit_tail
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat01_upcrossing_linear_horizon_spatial_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 ≤ z) (A : Set Ω)
    (hAmeas : MeasurableSet A)
    (hA : A ⊆ {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)})
    (t : ℝ) (htime : ∀ ω ∈ A, ENNReal.toReal (twoSidedExitUpTimeCorrected X z ω) ≤ t)
    (hlinear : 2 * (q * t) ≤ φ * z) :
    P A ≤ ENNReal.ofReal (Real.exp (-(φ * z) / 2)) := by sorry
