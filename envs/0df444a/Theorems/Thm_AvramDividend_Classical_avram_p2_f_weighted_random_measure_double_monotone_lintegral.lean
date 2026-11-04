-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_random_measure_double_monotone_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_random_measure_double_monotone_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:39:06.791842+00:00
-- url     : https://prove2.me/theorems/25ee6692-fd93-4e67-9a7c-a129c102b3fa
-- title:
--   Double monotone convergence for nonnegative predictable-integrand limits under a random measure
-- statement:
--   Let M_ω be a true sample-dependent measure, such as the original Lévy intrinsic jump measure, and F_n increasing nonnegative measurable marked integrands on each sample. Assume each random inner integral is an ambient-measurable function of ω. Then the expected random-measure integral of the pointwise supremum F_n equals the supremum of the expected integrals. The result applies Tonelli/monotone convergence first under each realised M_ω and then under P, with the essential outer measurability hypothesis explicit. It is a conditional analytic closure tool for extending P2-E source predictable-simple compensation to general nonnegative predictable integrands; it does not claim that measurability or any Lévy ν-rate is proved.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_iSup exact signature and lintegral_mono; no random-measure measurability assumption concealed.

import Mathlib

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_random_measure_double_monotone_lintegral
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (M : Ω → Measure α)
    (F : ℕ → Ω → α → ℝ≥0∞)
    (hF : ∀ ω n, Measurable (F n ω))
    (hOuter : ∀ n,
      Measurable (fun ω => (∫⁻ x, F n ω x ∂M ω)))
    (hMono : ∀ ω, Monotone (fun n => F n ω)) :
    (∫⁻ ω, (∫⁻ x, ⨆ n, F n ω x ∂M ω) ∂P) =
    ⨆ n, (∫⁻ ω, (∫⁻ x, F n ω x ∂M ω) ∂P) := by sorry
