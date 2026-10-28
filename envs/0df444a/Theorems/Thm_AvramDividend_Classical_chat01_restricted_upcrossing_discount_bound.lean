-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_restricted_upcrossing_discount_bound
-- name    : AvramDividend.Classical.chat01_restricted_upcrossing_discount_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:33:26.290594+00:00
-- url     : https://prove2.me/theorems/bfc5303f-9f0a-4ac4-a95f-9e92ef0029a3
-- title:
--   Positive Esscher-root discount bound for any restricted finite-upcrossing event
-- statement:
--   Given a q-positive-root φ and a nonnegative upcrossing level z, any extra event A contained in the event that the Lévy process upcrosses z in finite time inherits the universal exponential first-passage discount bound exp(-φz). This covers arbitrary additional lower-barrier, history, admissibility or stopping constraints once their inclusion in finite upcrossing is established. It is a reusable abstract conditional-exit reduction that avoids restating the stopped exponential martingale proof.
-- source:
--   Proved levy_positive_root_unrestricted_upcrossing_discount_bound (UUID eb6bd8bb-0632-4518-bc3e-590a6d258e8b) and ENNReal integral monotonicity. Independent of the open killed q-scale identity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_unrestricted_upcrossing_discount_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat01_restricted_upcrossing_discount_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 ≤ z) (A : Set Ω)
    (hA : A ⊆ {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)}) :
    (∫⁻ ω, A.indicator
      (fun ω => ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal
          (twoSidedExitUpTimeCorrected X z ω))))) ω ∂P) ≤
      ENNReal.ofReal (Real.exp (-(φ * z))) := by sorry
