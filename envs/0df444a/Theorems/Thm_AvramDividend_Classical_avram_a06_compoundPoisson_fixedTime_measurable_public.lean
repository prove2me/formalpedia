-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_fixedTime_measurable_public
-- name    : AvramDividend.Classical.avram_a06_compoundPoisson_fixedTime_measurable_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T17:53:34.642204+00:00
-- url     : https://prove2.me/theorems/b3ae2168-ea15-4463-95d4-59bf341e6e38
-- title:
--   Public fixed-time measurability of source-exact compound-Poisson sample path
-- statement:
--   For measurable interarrival and mark coordinate random variables, the canonical drift-plus-finite-jump-sum at any deterministic time is measurable, with no path monotonicity assumed for exceptional samples. This is required to prove real Laplace integrability for the original A06 Lévy record.
-- source:
--   Source-exact pinned LeanLevy CompoundPoisson.lean measurable_jumpCount_arrival and measurable_compoundPoisson proofs; rewritten in one public theorem to avoid private imports.

import Mathlib
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory Set ProbabilityTheory Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_compoundPoisson_fixedTime_measurable_public
    {Ω : Type*} [MeasurableSpace Ω] (b : ℝ)
    (τ Y : ℕ → Ω → ℝ)
    (hτ : ∀ n, Measurable (τ n))
    (hY : ∀ n, Measurable (Y n)) (t : ℝ) :
    Measurable (LevyFoundations.compoundPoisson b τ Y t) := by sorry
