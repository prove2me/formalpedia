-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_equal_mesh_increment_reversal_rectangles_ws01e_b
-- name    : AvramDividend.Classical.levy_equal_mesh_increment_reversal_rectangles_ws01e_b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T12:58:25.226017+00:00
-- url     : https://prove2.me/theorems/cdc97a00-8cba-41cb-8d8e-04243b2cf0bd
-- title:
--   Finite equal-mesh Lévy increments have their full rectangle law invariant under time reversal
-- statement:
--   For any genuine spectrally negative Lévy process, any nonnegative mesh width, any finite number of consecutive increments, and arbitrary Borel coordinate sets, the probability that the ordered increment vector lies in their product equals the probability that the reversed increment vector lies in the same product. This follows from stationary independent increments. It is the finite-grid law needed for fixed-horizon terminal-drawdown versus running-infimum reversal, without using Wiener–Hopf, two-sided exit or scale harmonicity.
-- source:
--   Stationary independent increments in the SpectrallyNegativeLevy axioms and finite-dimensional Lévy reversal; preparatory to the exponential-horizon Wiener–Hopf factorisation in Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes, §2.2 (https://warwick.ac.uk/fac/sci/statistics/staff/academic-research/kyprianou/scale-review-final.pdf).

import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Fin2
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finitePrefix_increment_rectangle_product

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_equal_mesh_increment_reversal_rectangles_ws01e_b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ)
    (B : Fin n → Set ℝ) (hB : ∀ i, MeasurableSet (B i)) :
    P {ω | (fun i : Fin n =>
      X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω) ∈ Set.pi Set.univ B} =
    P {ω | (fun i : Fin n =>
      X.X (((i.rev.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.rev.val : ℝ≥0) * δ) ω) ∈ Set.pi Set.univ B} := by sorry
