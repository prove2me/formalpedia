-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_stopped_scale_of_ae_upward_regularity
-- name    : AvramDividend.Classical.chat04_upper_endpoint_stopped_scale_of_ae_upward_regularity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:58:48.330892+00:00
-- url     : https://prove2.me/theorems/ecb37154-a1b2-4310-9f98-28efdba08c9c
-- title:
--   Stopped q-scale identity at the upper initial-reserve boundary under upward regularity
-- statement:
--   At initial reserve x=a>0, almost-sure upward regularity gives unit discounted upward-before-ruin expectation; multiplying by the q-scale value W(a) therefore recovers W(a). This proves the exact x=a boundary of the preferred stopped-scale theorem before the harder interior optional-stopping argument.
-- source:
--   Direct upper-endpoint specialization of root-connected stopped-scale target 09663d0d-c23e-47da-b5b9-1bbf28449a4d, using chat04_upper_endpoint_exit_expectation_of_ae_upward_regularity bf738dc2-2e7d-4823-9f6c-9e27fb2c3cf9.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_exit_expectation_of_ae_upward_regularity
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_upper_endpoint_stopped_scale_of_ae_upward_regularity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a : ℝ) (ha : 0 < a)
    (W : ℝ → ℝ)
    (hplus : ∀ᵐ ω ∂P,
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω) :
    twoSidedExitExpectation X q a a * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W a) := by sorry
