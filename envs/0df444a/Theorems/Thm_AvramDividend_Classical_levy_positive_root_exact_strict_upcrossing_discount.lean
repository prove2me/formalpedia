-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_positive_root_exact_strict_upcrossing_discount
-- name    : AvramDividend.Classical.levy_positive_root_exact_strict_upcrossing_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T12:54:20.026819+00:00
-- url     : https://prove2.me/theorems/0da3763f-17e2-414b-ac46-9b9f2088aa29
-- title:
--   Exact one-sided strict first-upcrossing Laplace transform at a positive Esscher root
-- statement:
--   For a spectrally negative Lévy process, positive discount q, positive exponent φ with ψ(φ)=q, and positive upper threshold z, the q-discounted expectation over finite strict first-upcrossing times equals exp(−φz). Uses the canonical corrected strict first passage clock, including the zero payoff when the clock is infinite. The currently Proved upper bound eb6bd8bb proves only one inequality; the reverse direction requires finite-grid optional stopping, a vanishing nohit remainder, no-positive-jump upper attainment and valid expectation convergence.
-- source:
--   Classical one-sided first-passage transform in Kyprianou, Introductory Lectures on Fluctuations of Lévy Processes, and Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions; precise clock and integrand adapted from Proved bound eb6bd8bb-0632-4518-bc3e-590a6d258e8b.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_unrestricted_upcrossing_discount_bound
import Mathlib

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_positive_root_exact_strict_upcrossing_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 < z) :
    (∫⁻ ω, if twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)
       then ENNReal.ofReal
         (Real.exp (-(q * ENNReal.toReal
           (twoSidedExitUpTimeCorrected X z ω))))
       else 0 ∂P) =
    ENNReal.ofReal (Real.exp (-(φ * z))) := by sorry
