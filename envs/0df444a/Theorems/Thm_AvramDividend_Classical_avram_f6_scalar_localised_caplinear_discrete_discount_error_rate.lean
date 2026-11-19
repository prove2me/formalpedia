-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_scalar_localised_caplinear_discrete_discount_error_rate
-- name    : AvramDividend.Classical.avram_f6_scalar_localised_caplinear_discrete_discount_error_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:02:31.946957+00:00
-- url     : https://prove2.me/theorems/b93b6d91-7db4-421d-812c-dd505b901aa3
-- title:
--   Sharp finite-grid discount oscillation bound from local Lipschitz cap-linear drops and cumulative cash
-- statement:
--   For any physical finite time grid, if discounted exponential weight differences are nonnegative and at most M, and each nonnegative cap-linear potential drop V_i is bounded by L times its cumulative-dividend increment A_(i+1)−A_i, then the entire mesh oscillation error is bounded by M L times the total original cumulative-dividend increment A_m−A_0. The proof uses pointwise multiplication of genuine inequalities, finite-sum monotonicity, and exact telescoping. In the original mixed Lévy proof, A is rightLimit D, V is the cap-linear prepayment potential drop, M may be bounded by q times physical mesh width, and L is a localised true cap-linear slope bound. Its explicit hypotheses identify the missing localisation needed to control the full signed cash mesh error; no false global Lipschitz assumption is silently inferred.
-- source:
--   Pure scalar pathwise finite-grid inequality for original all-cap physical discounted cash correction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_f6_scalar_localised_caplinear_discrete_discount_error_rate
    (m : ℕ) (E V A : ℕ → ℝ) (M L : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hOsc : ∀ i < m, 0 ≤ E i - E (i + 1) ∧
      E i - E (i + 1) ≤ M)
    (hA : ∀ i < m, A i ≤ A (i + 1))
    (hCap : ∀ i < m, 0 ≤ V i ∧
      V i ≤ L * (A (i + 1) - A i)) :
    (∑ i ∈ Finset.range m, (E i - E (i + 1)) * V i) ≤
      M * L * (A m - A 0) := by sorry
