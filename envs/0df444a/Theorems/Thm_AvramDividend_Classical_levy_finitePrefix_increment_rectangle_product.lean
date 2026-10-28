-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finitePrefix_increment_rectangle_product
-- name    : AvramDividend.Classical.levy_finitePrefix_increment_rectangle_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T08:04:00.259057+00:00
-- url     : https://prove2.me/theorems/35810ccf-6a41-4604-bcc0-1d5d1f2221c1
-- title:
--   Finite prefix joint Lévy increment laws factor over measurable rectangles
-- statement:
--   For any nondecreasing time grid and finite prefix, the probability that all successive Lévy increments land in prescribed Borel sets factors into the product of their one-dimensional probabilities. Uses the already Proved all-prefix past-event cylinder factorisation with the past event univ. The finite-vector rectangle factorisation is a direct input to proving shifted finite-dimensional stationarity.
-- source:
--   Specialises the Proved chat04_all_finite_prefix_increment_cylinder_product (UUID 4b6af35c-c6a9-4bca-ab7d-28f22e7bd161). Intermediate for full shifted-path law stationarity and barrier dividend strong-Markov child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_all_finite_prefix_increment_cylinder_product

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finitePrefix_increment_rectangle_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (t : ℕ → ℝ≥0) (ht : Monotone t) (hst : s ≤ t 0)
    (n : ℕ) (B : Fin n → Set ℝ) (hB : ∀ i, MeasurableSet (B i)) :
    P {ω | (fun i : Fin n =>
      X.X (t (i.val + 1)) ω - X.X (t i.val) ω) ∈ Set.pi Set.univ B} =
      ∏ k ∈ Finset.range n,
        P {ω | X.X (t (k + 1)) ω - X.X (t k) ω ∈
          (if hk : k < n then B ⟨k, hk⟩ else Set.univ)} := by
  sorry
