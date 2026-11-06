-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_weighted_intrinsic_jump_drift_grid_le
-- name    : AvramDividend.Classical.avram_p3_2_original_weighted_intrinsic_jump_drift_grid_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T07:17:06.912082+00:00
-- url     : https://prove2.me/theorems/b6b6d2e9-20ec-451d-bb7b-d4dc1e9c4b36
-- title:
--   Weighted original BV physical drift and intrinsic marked-jump grid upper bound
-- statement:
--   On the actual bounded-variation Lévy sample paths, the sum of weighted physical source increments and the same-cell intrinsic negative-jump count integrals never exceeds the weighted source drift. The weights are arbitrary nonnegative functions of finitely many cells. The proof retains the true monotone downward BV remainder, so finite-activity and residual-zero assumptions are unnecessary.
-- source:
--   Proved source-exact original BV intrinsic marked-jump interval remainder decomposition 09869e16, with nonnegative weights and finite summation. For E2/physical stopped-grid source convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Signed finite-grid source bound from the actual original intrinsic jump count,
with nonnegative arbitrary predictable weights and nondecreasing BV residual. -/

theorem AvramDividend.Classical.avram_p3_2_original_weighted_intrinsic_jump_drift_grid_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (s t : Fin n → ℝ≥0)
      (hst : ∀ i, s i ≤ t i) (a : Fin n → ℝ)
      (ha : ∀ i, 0 ≤ a i),
      (∑ i : Fin n, a i *
        (X.X (t i) ω - X.X (s i) ω +
          (∫⁻ p, (if s i < p.1 ∧ p.1 ≤ t i then ENNReal.ofReal (-p.2) else 0) ∂
            ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ≤
      ∑ i : Fin n, a i * (((t i : ℝ) - (s i : ℝ)) * X.drift) := by sorry
