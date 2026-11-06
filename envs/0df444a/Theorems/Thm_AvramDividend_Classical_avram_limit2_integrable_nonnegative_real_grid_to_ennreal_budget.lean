-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_integrable_nonnegative_real_grid_to_ennreal_budget
-- name    : AvramDividend.Classical.avram_limit2_integrable_nonnegative_real_grid_to_ennreal_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:53:44.569229+00:00
-- url     : https://prove2.me/theorems/36b438d7-704d-4bff-b537-72d1b8fbd679
-- title:
--   Exact nonnegative real stopped-grid expectations imply uniform ENNReal lintegral bounds
-- statement:
--   For the real F_n of an original source stochastic grid certificate with Integrable and almost everywhere nonnegative F_n, the real expected-value bound for every n yields the corresponding ENNReal lintegral budget. This uses pinned Mathlib's ofReal_integral_eq_lintegral_ofReal and ENNReal.ofReal monotonicity. The added source preamble imports are required because the previous targeting attempt lacked real integrals and the Avram namespace; the mathematical statement is unchanged.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_integrable_nonnegative_real_grid_to_ennreal_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (F : ℕ → Ω → ℝ) (B : ℝ)
    (hInt : ∀ n, Integrable (F n) P)
    (hNonneg : ∀ n, ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hMean : ∀ n, (∫ ω, F n ω ∂P) ≤ B) :
    ∀ n : ℕ, (∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) ≤
      ENNReal.ofReal B := by sorry
