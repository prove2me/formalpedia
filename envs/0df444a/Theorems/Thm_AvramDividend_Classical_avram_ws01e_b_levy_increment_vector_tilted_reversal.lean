-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_increment_vector_tilted_reversal
-- name    : AvramDividend.Classical.avram_ws01e_b_levy_increment_vector_tilted_reversal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T07:47:40.55284+00:00
-- url     : https://prove2.me/theorems/a712024a-bd4b-4fbe-a3a5-9e94d600d5e7
-- title:
--   Finite-mesh Lévy increment reversal survives any reversal-invariant density tilt
-- statement:
--   For a genuine spectrally negative Lévy process and a finite equal-mesh vector of its path increments, a nonnegative measurable density on the increment-vector state space which is invariant under reversing the increment coordinates preserves the equality of probabilities of any Borel vector event and its reverse preimage. This follows from the accepted equality of the unweighted full-vector law under reversal and the accepted general symmetry-preserving change-of-measure theorem, and is an exact finite-dimensional Esscher prerequisite (Esscher densities depend on the sum of increments and so meet the invariant-density condition).
-- source:
--   Proved levy_equal_mesh_increment_vector_law_reversal_ws01e_b (b78d5f90) and avram_ws01e_b_withDensity_preserves_measurable_symmetry (d04f8b9f).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_equal_mesh_increment_vector_law_reversal_ws01e_b
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_withDensity_preserves_measurable_symmetry

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_levy_increment_vector_tilted_reversal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (δ : ℝ≥0) (n : ℕ)
    (w : (Fin n → ℝ) → ℝ≥0∞) (hw : Measurable w)
    (hwR : ∀ v : Fin n → ℝ, w (fun i => v i.rev) = w v)
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    ((Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
      X.X ((i.val : ℝ≥0) * δ) ω) P).withDensity w)
      {v : Fin n → ℝ | (fun i => v i.rev) ∈ A} =
    ((Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
      X.X ((i.val : ℝ≥0) * δ) ω) P).withDensity w) A := by sorry
