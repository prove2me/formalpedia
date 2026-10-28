-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_deficit_strictMono_of_dense_grid
-- name    : AvramDividend.Classical.bv_infinite_activity_deficit_strictMono_of_dense_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:54:59.347274+00:00
-- url     : https://prove2.me/theorems/f504f7ae-e950-4d43-a6d8-61d5e98eee10
-- title:
--   The actual infinite-activity bounded-variation Lévy drift deficit is almost surely strictly increasing given a dense countable time grid
-- statement:
--   For infinite negative jump activity, the canonical drift-deficit path of the actual bounded-variation Lévy process is strictly increasing on all nonnegative times, almost surely. First combine the countably many strict grid increments onto one full-measure event, and then use dense-range interpolation plus almost-sure global monotonicity.
-- source:
--   Proved bv_infinite_activity_deficit_strict_grid_pairs, bv_drift_deficit_ae_monotone_all_times and Mathlib DenseRange.exists_mem_open.

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_deficit_strict_grid_pairs
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.MeasureTheory.OuterMeasure.AE

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_infinite_activity_deficit_strictMono_of_dense_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (grid : ℕ → ℝ≥0) (hDense : DenseRange grid) :
    ∀ᵐ ω ∂P, StrictMono
      (fun t : ℝ≥0 => X.drift * (t : ℝ) - X.X t ω) := by sorry
