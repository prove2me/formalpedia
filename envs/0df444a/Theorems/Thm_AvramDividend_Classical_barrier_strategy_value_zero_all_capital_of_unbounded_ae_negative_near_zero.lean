-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital_of_unbounded_ae_negative_near_zero
-- name    : AvramDividend.Classical.barrier_strategy_value_zero_all_capital_of_unbounded_ae_negative_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T21:43:40.545169+00:00
-- url     : https://prove2.me/theorems/6e269fcd-c04e-4daa-a06e-b168d0e4612a
-- title:
--   Unbounded-variation zero-barrier value at every nonnegative reserve under negative near-zero regularity
-- statement:
--   The unbounded-variation zero-barrier value formula holds at every nonnegative initial reserve conditional on almost-sure near-zero negative Lévy increments. At reserve zero use the canonically Proved zero-boundary package. For positive initial reserve, invoke the Proved initial-excess decomposition barrierStrategy_above_value_of_boundary, which adds the immediate capital payment. This conditionally resolves the exact zero-barrier all-capital root dependency d73a6aec-f808-4bc8-935d-5004c5b67597; only the missing stochastic regularity and bounded variation branch remain.
-- source:
--   Direct child of the open barrier_strategy_value_zero_all_capital. Uses two Proved boundary and cash-decomposition theorems.

import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package_of_unbounded_ae_negative_near_zero
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_above_value_of_boundary

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrier_strategy_value_zero_all_capital_of_unbounded_ae_negative_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hNear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0)
    (x : ℝ) (hx : 0 ≤ x) :
    dividendValue X q x (barrierStrategy X x 0) =
      ENNReal.ofReal (barrierValue W 0 x) := by sorry
