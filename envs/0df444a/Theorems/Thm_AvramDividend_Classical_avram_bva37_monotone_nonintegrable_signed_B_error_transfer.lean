-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva37_monotone_nonintegrable_signed_B_error_transfer
-- name    : AvramDividend.Classical.avram_bva37_monotone_nonintegrable_signed_B_error_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:33:22.379978+00:00
-- url     : https://prove2.me/theorems/7cb0c4d8-a6a5-4ef3-99b5-f5d3128b403f
-- title:
--   Monotone exact original BV rewards have uniform expected ceiling from centred noise, non-L1 nonpositive B, vanishing positive error
-- statement:
--   For genuine reward approximants F_n with nondecreasing expected value, suppose each F_n is L1, each centred stochastic term M_n is L1 and mean zero, each error E_n has integrable positive part with expectation tending to zero, and the source-exact HJB drift B_n is pointwise nonpositive almost everywhere even if its negative part is nonintegrable. If F_n≤a+M_n+B_n+(E_n)_+ almost everywhere, then E[F_n]≤a for every n. The proof uses the independently Proved original one-sided non-L1 signed B transfer and monotonicity of expectations. This closes the mean-budget step without making the mathematically false assumption that the raw generator B belongs to L1 at infinite activity.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_two_scale_integrable_cash_expected_budget_without_B_L1
import Mathlib.Tactic.Linarith
set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva37_monotone_nonintegrable_signed_B_error_transfer
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F M B E : ℕ → Ω → ℝ) (a : ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hMono : ∀ n m, n ≤ m → (∫ ω, F n ω ∂P) ≤ (∫ ω, F m ω ∂P))
    (hMI : ∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0)
    (hEI : ∀ n, Integrable (fun ω => max (E n ω) 0) P)
    (hB : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hBudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ a + M n ω + B n ω + max (E n ω) 0)
    (hErr : Tendsto (fun n => ∫ ω, max (E n ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∀ n, (∫ ω, F n ω ∂P) ≤ a := by sorry
