-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_stopped_scale_of_ae_up_clock
-- name    : AvramDividend.Classical.chat04_upper_endpoint_stopped_scale_of_ae_up_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:21:45.51999+00:00
-- url     : https://prove2.me/theorems/9aa27701-f49f-48c2-b051-7e6e507ee3d1
-- title:
--   Upper-endpoint stopped q-scale identity requiring only instantaneous upward first passage
-- statement:
--   For a positive upper barrier a and a spectrally negative Lévy process starting at zero, the downward clock below -a is automatically positive. Thus if the strict upward clock above zero is instantaneously zero almost surely, the upward-before-ruin discount integral is one and multiplication by the q-scale value W(a) gives the exact stopped-scale boundary identity at x=a.
-- source:
--   Direct use of Proved chat04_upper_endpoint_two_sided_exit_expectation_one 4f871287-bf29-4860-8d54-596d7d7b830b and newly published chat04_down_exit_time_pos_ae_of_positive_barrier 1b5e8224-8cb8-4bd5-8266-e35e1c7b7db0. This exact endpoint is a specialisation of the canonical stopped-scale target 09663d0d-c23e-47da-b5b9-1bbf28449a4d.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_down_exit_time_pos_ae_of_positive_barrier
import Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_two_sided_exit_expectation_one
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_upper_endpoint_stopped_scale_of_ae_up_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a : ℝ) (ha : 0 < a)
    (W : ℝ → ℝ)
    (hup0 : ∀ᵐ ω ∂P, twoSidedExitUpTime X 0 ω = 0) :
    twoSidedExitExpectation X q a a * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W a) := by sorry
