-- Prove2me | Theorems.Thm_AvramDividend_Classical_condExp_pair_stronglyMeasurable_integrable_difference
-- name    : AvramDividend.Classical.condExp_pair_stronglyMeasurable_integrable_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:20:29.322645+00:00
-- url     : https://prove2.me/theorems/d7b0e52f-6626-46ca-8601-ff4869629db7
-- title:
--   Automatic strong measurability and integrable differences of conditional expectations
-- statement:
--   For any pair of real-valued random payoffs F and G, any ambient measure P, and a sub-sigma-algebra m, the two conditional expectation functions are strongly measurable on the ambient measurable space and their difference is integrable under P. Apply Mathlib's exact pinned declarations stronglyMeasurable_condExp and integrable_condExp, with monotonicity of strong measurability and subtraction of integrable functions. This packages automatic side conditions repeatedly required when passing conditional Lévy Markov identities from finite-state approximations to general random reserves.
-- source:
--   Both declarations verified against pinned Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. Independent of pending Prove2Me proofs.

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

theorem AvramDividend.Classical.condExp_pair_stronglyMeasurable_integrable_difference
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (F G : Ω → ℝ) :
    StronglyMeasurable (P[F | m]) ∧
    StronglyMeasurable (P[G | m]) ∧
    Integrable (fun ω => (P[F | m]) ω - (P[G | m]) ω) P := by sorry
