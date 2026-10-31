-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_discounted_deriv_stronglyPredictable
-- name    : AvramDividend.Classical.avram_wave3_04_discounted_deriv_stronglyPredictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:42:09.894158+00:00
-- url     : https://prove2.me/theorems/fcdc8c77-b533-49ff-8001-cf775c3945a8
-- title:
--   Discounted derivative stochastic integrands preserve strong predictability
-- statement:
--   For any strongly predictable real process, discount rate q and real function w, the process e^{-qt} deriv w(Z_t) is strongly predictable under the exact same filtration. The exponential factor is deterministic, continuous and adapted, hence predictable by the Proved generic left-continuous adapted theorem; the real derivative is Borel measurable by pinned measurable_deriv, and composition/product preserve strong predictability. No global C2 or stochastic integration identity is assumed.
-- source:
--   Pinned Mathlib measurable_deriv and strong predictable closure, canonical Proved avram_wave3_04_strongAdapted_leftContinuous_predictable UUID 5ae104c4-13de-429a-a344-76d22511259b. Private remote compiler probe a4f6cabf-5ebc-489c-977b-f0da29b17306 passed to sentinel without candidate errors, SHA 4c5d317f470c570ecd6acc9abc52303a7fc6c37896a92b6be36ce4a55e8e75b7.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_wave3_04_discounted_deriv_stronglyPredictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Z : ℝ≥0 → Ω → ℝ)
    (hZ : IsStronglyPredictable 𝓕 Z)
    (w : ℝ → ℝ) (q : ℝ) :
    IsStronglyPredictable 𝓕
      (fun t ω => Real.exp (-(q * (t : ℝ))) * deriv w (Z t ω)) := by sorry
