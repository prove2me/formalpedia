-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_occupation_bind_sections_integrable_public
-- name    : AvramDividend.Classical.avram_chat24_occupation_bind_sections_integrable_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T14:11:29.401144+00:00
-- url     : https://prove2.me/theorems/92887d5d-0a99-4615-aac3-82860fb3c907
-- title:
--   Occupation bind L1 gives almost-everywhere section L1
-- statement:
--   Norm Fubini for a measurable occupation kernel K: Integrable H of P.bind K entails a.e. integrability under K ω. This is the exact source-integrability bridge in 10ef35ab. Public prerequisite for the public actual-stopped integrability target.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_chat24_occupation_bind_sections_integrable_public
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) (K : Ω → Measure β) (hK : AEMeasurable K P)
    (H : β → ℝ) (hHm : Measurable H) (hHi : Integrable H (P.bind K)) :
    ∀ᵐ ω ∂P, Integrable H (K ω) := by sorry
