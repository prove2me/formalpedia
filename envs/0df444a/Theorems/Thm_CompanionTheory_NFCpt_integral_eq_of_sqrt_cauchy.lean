-- Prove2me | Theorems.Thm_CompanionTheory_NFCpt_integral_eq_of_sqrt_cauchy
-- name    : CompanionTheory.NFCpt.integral_eq_of_sqrt_cauchy
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:18:40.073389+00:00
-- url     : https://prove2.me/theorems/3c6afd4d-07f0-4f09-9f6d-7e0b81680c65
-- title:
--   NFCpt: integral eq of sqrt cauchy
-- statement:
--   The NFCpt construction uses the integral eq of sqrt cauchy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/DiscreteGroupWaves/IntegralEqOfSqrtCauchy.lean#L101-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/DiscreteGroupWaves/IntegralEqOfSqrtCauchy.lean#L101-L162

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_DiscreteGroupWaves_IntegralEqOfSqrtCauchy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.NFCpt
open MeasureTheory Filter Topology

theorem CompanionTheory.NFCpt.integral_eq_of_sqrt_cauchy {α : Type*} [MeasurableSpace α] {μ : Measure α} {q : ℕ → α → ℝ} {v : α → ℝ}
    {d : ℕ → ℕ → α → ℝ} {a : ℝ} (hq : ∀ n, Integrable (q n) μ) (hq0 : ∀ n x, 0 ≤ q n x)
    (hd : ∀ n m, Integrable (d n m) μ) (hd0 : ∀ n m x, 0 ≤ d n m x)
    (htri : ∀ n m x, |Real.sqrt (q n x) - Real.sqrt (q m x)| ≤ Real.sqrt (d n m x))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => q n x) atTop (𝓝 (v x)))
    (ha : Tendsto (fun n => ∫ x, q n x ∂μ) atTop (𝓝 a))
    (hC : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n m, N ≤ n → N ≤ m → ∫ x, d n m x ∂μ ≤ η) :
    Integrable v μ ∧ ∫ x, v x ∂μ = a := by sorry
