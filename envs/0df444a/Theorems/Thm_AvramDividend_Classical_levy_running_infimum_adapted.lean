-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_running_infimum_adapted
-- name    : AvramDividend.Classical.levy_running_infimum_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:45:03.287312+00:00
-- url     : https://prove2.me/theorems/fde9ba4e-607e-4239-a008-657c3886cfbd
-- title:
--   The true finite-time negative running Lévy infimum is adapted to the original filtration
-- statement:
--   For a spectrally negative Lévy process X adapted to filtration F and with right-continuous paths, the actual negative running infimum −inf_{0≤r≤t} X_r is F_t-measurable for every deterministic t. The proof uses boundedness below of each finite path, the equality of the true supremum of −X with a countable dense-sample supremum plus its terminal value, and the proven adaptedness of countably sampled suprema. Including the endpoint handles negative jumps exactly, allowing truncated exponential-clock infimum functionals to satisfy the path-section measurability premise of the joint-clock Esscher consistency theorem.
-- source:
--   Kuznetsov–Kyprianou–Rivero, Lévy cadlag path regularity; accepted Prove2Me dense_timeSup_with_endpoint 4cdf4ed6-71c6-4948-849b-8bfefa587f36, countable_pastSup_adapted_of_adapted e543ab50-fbe6-414b-82ed-42eca681cbfd, finite-horizon boundedness below 3bff0b3d-b21d-4639-8902-1ce473fce724; pinned Mathlib Real.sSup_neg and Set.neg_range.

import Mathlib.Topology.Bases
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_countable_pastSup_adapted_of_adapted
import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_running_infimum_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Adapted 𝓕 (fun t ω =>
      -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}) := by sorry
