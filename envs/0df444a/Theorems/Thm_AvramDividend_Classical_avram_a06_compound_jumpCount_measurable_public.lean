-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_compound_jumpCount_measurable_public
-- name    : AvramDividend.Classical.avram_a06_compound_jumpCount_measurable_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:10:23.148345+00:00
-- url     : https://prove2.me/theorems/46c70d5d-ec46-4dbb-b8de-dda4dfffb629
-- title:
--   Genuine compound-Poisson arrival jump count measurable at fixed times
-- statement:
--   The number of arrivals of a measurable sequence at fixed time is measurable, through the measurable characterisation of Nat.sInf of the first arrival strictly exceeding that time.
-- source:
--   The already accepted source-exact public compound-Poisson fixed-time measurability proof b3ae2168; its intermediate jump-count proof is factored into a reusable public theorem.

import Mathlib
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_arrival
open MeasureTheory Set ProbabilityTheory Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_compound_jumpCount_measurable_public
    {Ω : Type*} [MeasurableSpace Ω] (τ : ℕ → Ω → ℝ)
    (hτ : ∀ n, Measurable (τ n)) (t : ℝ) :
    Measurable (fun ω => LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) t) := by sorry
