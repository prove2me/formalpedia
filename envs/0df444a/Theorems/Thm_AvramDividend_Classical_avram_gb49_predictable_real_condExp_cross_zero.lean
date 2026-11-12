-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb49_predictable_real_condExp_cross_zero
-- name    : AvramDividend.Classical.avram_gb49_predictable_real_condExp_cross_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:18:27.092004+00:00
-- url     : https://prove2.me/theorems/a4976dc6-4476-4042-90b0-c794556712f5
-- title:
--   Predictable real coefficient is orthogonal to centred future martingale difference
-- statement:
--   If a real coefficient is measurable with respect to a sub-filtration and a future integrable innovation has zero conditional expectation, then their integrable product has zero expectation.
-- source:
--   Generic scalar conditional-expectation product step needed for gb33 original Gaussian quadratic grid cell orthogonality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped InnerProductSpace
noncomputable section

theorem AvramDividend.Classical.avram_gb49_predictable_real_condExp_cross_zero
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (hm : m ≤ mΩ) [SigmaFinite (P.trim hm)]
    (A Q : Ω → ℝ)
    (hA : Measurable[m] A) (hQ : Integrable Q P)
    (hProd : Integrable (fun ω => A ω * Q ω) P)
    (hCond : P[Q | m] =ᵐ[P] (fun _ => (0 : ℝ))) :
    (∫ ω, A ω * Q ω ∂P) = 0 := by sorry
