-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gauss_endpoint_sigma_pos_of_zero_nu_unbounded
-- name    : AvramDividend.Classical.avram_gauss_endpoint_sigma_pos_of_zero_nu_unbounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T13:09:30.197385+00:00
-- url     : https://prove2.me/theorems/0708699f-4ead-4549-b868-e055b7a82d21
-- title:
--   Original zero-jump unbounded-variation Gaussian coefficient strictly positive
-- statement:
--   On the genuine original process, a zero jump measure and failure of bounded variation imply a strictly positive Gaussian coefficient. This gives the positive square bracket parameter needed for the Gaussian stopped Itô budget.
-- source:
--   Exact corollary of public Proved a74e690b and the nonnegative Gaussian coefficient field of SpectrallyNegativeLevy. Root-connected prerequisites 642de490 and d65c7756.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gauss_endpoint_sigma_pos_of_zero_nu_unbounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hBV : ¬ X.BoundedVariation) :
    0 < X.σ := by sorry
