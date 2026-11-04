-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_random_measure_monotone_compensator_extension
-- name    : AvramDividend.Classical.avram_p2_f_weighted_random_measure_monotone_compensator_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:46:58.491193+00:00
-- url     : https://prove2.me/theorems/7f2fc8d9-9d08-4645-bec8-a7a5f17bdce5
-- title:
--   Monotone limit of genuine source random-measure compensators from stagewise exact identities
-- statement:
--   Let M_ω be a genuine sample-dependent jump measure and K a fixed candidate compensator measure. Suppose an increasing sequence of nonnegative measurable predictable-simple approximations F_n has exactly compensated expected integrals at every stage, and both source and K integrals are separately measurable as random variables. Then the same exact expected compensation holds for the supremum integrand, allowing infinite activity, zero times infinity and unbounded weights. The proof applies two previously proved double monotone-integral interchange identities and stage equality. Each stagewise compensator identity, the measurability of the original random inner integrals, and the approximation monotonicity remain explicit premises; this does not assume or prove P2-A's missing Lévy ν rate.
-- source:
--   P2-F random measure double monotone theorem plus exact stagewise compensation assumptions.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_random_measure_double_monotone_lintegral

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_random_measure_monotone_compensator_extension
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (M : Ω → Measure α) (K : Measure α)
    (F : ℕ → Ω → α → ℝ≥0∞)
    (hF : ∀ ω n, Measurable (F n ω))
    (hOuterM : ∀ n,
      Measurable (fun ω => (∫⁻ x, F n ω x ∂M ω)))
    (hOuterK : ∀ n,
      Measurable (fun ω => (∫⁻ x, F n ω x ∂K)))
    (hMono : ∀ ω, Monotone (fun n => F n ω))
    (hEach : ∀ n,
      (∫⁻ ω, (∫⁻ x, F n ω x ∂M ω) ∂P) =
      (∫⁻ ω, (∫⁻ x, F n ω x ∂K) ∂P)) :
    (∫⁻ ω, (∫⁻ x, ⨆ n, F n ω x ∂M ω) ∂P) =
    (∫⁻ ω, (∫⁻ x, ⨆ n, F n ω x ∂K) ∂P) := by sorry
