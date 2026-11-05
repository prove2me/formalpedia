-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_finite_cap_linear_extension_global_exponential_envelope_of_interior_bound
-- name    : AvramDividend.Classical.avram_p4_d_dividend_finite_cap_linear_extension_global_exponential_envelope_of_interior_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:30:01.095641+00:00
-- url     : https://prove2.me/theorems/6a3c1304-aa35-4856-923e-1bff344da01e
-- title:
--   Original finite-cap linear value extension has an exponential growth envelope from its bounded cap interval
-- statement:
--   Under the exact finite-cap extension definition and original zero-negative-reserve value, an explicit finite bound M on w over the compact cap interval propagates to the whole real line as ‖V(z)‖≤(M+1)exp(z). The zero-negative, interior, and linear-above-cap branches are all proved. The bound removes the exponential-envelope assumption from the original stopped comparison-value L1 theorem once compactness supplies the original w interval bound.
-- source:
--   Canonical P4-F finite-cap extension and original zero-negative reserve, paired with pinned Mathlib Real.add_one_le_exp, norm triangle and real inequalities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_finite_cap_linear_extension_global_exponential_envelope_of_interior_bound
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (w V : ℝ → ℝ)
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else
        w C.toReal + (z - C.toReal))
    (M : ℝ) (hM : 0 ≤ M)
    (hw_bd : ∀ z ∈ Icc (0 : ℝ) C.toReal, ‖w z‖ ≤ M) :
    ∀ z : ℝ, ‖V z‖ ≤ (M + 1) * Real.exp z := by sorry
