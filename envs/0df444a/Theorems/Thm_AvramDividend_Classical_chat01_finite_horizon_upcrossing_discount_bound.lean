-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_finite_horizon_upcrossing_discount_bound
-- name    : AvramDividend.Classical.chat01_finite_horizon_upcrossing_discount_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:41:47.652764+00:00
-- url     : https://prove2.me/theorems/f9fb9970-a4ce-482e-800f-d6ef4ab30f0d
-- title:
--   Finite-horizon upcrossing event mass discount estimate at a positive Esscher root
-- statement:
--   For a spectrally negative Lévy process with positive Esscher q-root, any finite-upcrossing event whose passage clock is bounded above by a fixed horizon t satisfies an exponentially decaying upper bound on its constant-horizon discounted event mass. No measurability of the restricting event is needed for the integral formulation. This is the finite-horizon counterpart of the Proved unrestricted stopping-clock estimate, reusable for first-passage grid limits and killing constraints.
-- source:
--   Proved levy_positive_root_unrestricted_upcrossing_discount_bound (eb6bd8bb-0632-4518-bc3e-590a6d258e8b) and ENNReal lintegral monotonicity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_unrestricted_upcrossing_discount_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat01_finite_horizon_upcrossing_discount_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 ≤ z) (A : Set Ω)
    (hA : A ⊆ {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)})
    (t : ℝ) (htime : ∀ ω ∈ A, ENNReal.toReal (twoSidedExitUpTimeCorrected X z ω) ≤ t) :
    (∫⁻ ω, A.indicator (fun _ : Ω => ENNReal.ofReal (Real.exp (-(q * t)))) ω ∂P) ≤
      ENNReal.ofReal (Real.exp (-(φ * z))) := by sorry
