-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_equal_mesh_increment_vector_law_reversal_ws01e_b
-- name    : AvramDividend.Classical.levy_equal_mesh_increment_vector_law_reversal_ws01e_b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:26:25.787013+00:00
-- url     : https://prove2.me/theorems/b78d5f90-43d4-4229-9f1a-23b5c29a59a7
-- title:
--   Entire equal-mesh Lévy increment-vector law is invariant under coordinate reversal
-- statement:
--   For a genuine spectrally negative Lévy process and arbitrary finite equal-time mesh, the pushforward probability distribution of the ordered increment vector in the measurable finite product of real lines equals that of its coordinate reversal. This upgrades the canonically Proved Borel-rectangle identity to full distributional equality and permits arbitrary measurable finite-grid extrema functionals to be transported by measure-map congruence.
-- source:
--   Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes, §2.1 Wiener–Hopf factorisation and Lévy path reversal (https://warwick.ac.uk/fac/sci/statistics/staff/academic-research/kyprianou/scale-review-final.pdf); derived from Prove2Me Proved rectangle theorem cdc97a00-8cba-41cb-8d8e-04243b2cf0bd and Proved piPathMeasure_eq_of_finite_cylinder_masses.

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Theorems.Thm_AvramDividend_Classical_piPathMeasure_eq_of_finite_cylinder_masses
import Theorems.Thm_AvramDividend_Classical_levy_equal_mesh_increment_reversal_rectangles_ws01e_b

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_equal_mesh_increment_vector_law_reversal_ws01e_b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (δ : ℝ≥0) (n : ℕ) :
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω) P =
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (((i.rev.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.rev.val : ℝ≥0) * δ) ω) P := by sorry
