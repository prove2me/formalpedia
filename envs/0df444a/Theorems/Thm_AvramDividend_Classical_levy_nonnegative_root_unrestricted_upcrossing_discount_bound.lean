-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_nonnegative_root_unrestricted_upcrossing_discount_bound
-- name    : AvramDividend.Classical.levy_nonnegative_root_unrestricted_upcrossing_discount_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:54:52.331412+00:00
-- url     : https://prove2.me/theorems/12fbdda4-765b-4ae6-a0e6-6f8a30895236
-- title:
--   Nonnegative-root discounted unrestricted upward passage bound including zero discount
-- statement:
--   For all nonnegative discounts and nonnegative matching roots of a spectrally negative Levy Laplace exponent, unrestricted discounted upward passage at a nonnegative level is bounded by the exponential root factor, including zero discount. Needed for true excursion-height survival upper bound in Kyprianou Chapter 8 Lemma 8.2.
-- source:
--   Direct adaptation of remotely Proved ec89766b-52bf-4d3a-aa92-f14ee3c6ff63 and eb6bd8bb-0632-4518-bc3e-590a6d258e8b; root martingale estimate 79ea4eef-a91a-414b-99fb-5f4e4668e8e1 and grid-to-passage theorem c35e351b-bb7b-41d4-9138-fb859c5f8868 assume only nonnegative root and discount.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem AvramDividend.Classical.levy_nonnegative_root_unrestricted_upcrossing_discount_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (φ : ℝ) (hφ : 0 ≤ φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 ≤ z) :
    (∫⁻ ω, if twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)
       then ENNReal.ofReal
         (Real.exp (-(q * ENNReal.toReal
           (twoSidedExitUpTimeCorrected X z ω))))
       else 0 ∂P) ≤ ENNReal.ofReal (Real.exp (-(φ * z))) := by sorry
