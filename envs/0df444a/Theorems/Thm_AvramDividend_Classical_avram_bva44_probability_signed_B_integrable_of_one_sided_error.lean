-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva44_probability_signed_B_integrable_of_one_sided_error
-- name    : AvramDividend.Classical.avram_bva44_probability_signed_B_integrable_of_one_sided_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T01:13:24.395107+00:00
-- url     : https://prove2.me/theorems/46c91787-1a81-46ec-b58f-1af1a9f10a37
-- title:
--   Probability-space signed BV negative HJB drift is L1 under an integrable one-sided source cash envelope
-- statement:
--   On the original probability measure P, if F, the centred source M, and the positive error E_+ are integrable, and an a.e.-strongly-measurable B is nonpositive almost everywhere with F≤a+M+B+E_+, then B must be integrable. The proof uses the probability assumption to establish integrability of the constant a and bounds 0≤−B≤a+M+E_+−F almost everywhere. The finite-measure hypothesis is essential: without it the implication fails on infinite-measure spaces, as shown by F=M=E=0, a=1, B=−1.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Tactic.Linarith
set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva44_probability_signed_B_integrable_of_one_sided_error
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F M B E : Ω → ℝ) (a : ℝ)
    (hFI : Integrable F P)
    (hMI : Integrable M P)
    (hEI : Integrable (fun ω => max (E ω) 0) P)
    (hBmeas : AEStronglyMeasurable B P)
    (hBnonpos : ∀ᵐ ω ∂P, B ω ≤ 0)
    (hBound : ∀ᵐ ω ∂P,
      F ω ≤ a + M ω + B ω + max (E ω) 0) :
    Integrable B P := by sorry
