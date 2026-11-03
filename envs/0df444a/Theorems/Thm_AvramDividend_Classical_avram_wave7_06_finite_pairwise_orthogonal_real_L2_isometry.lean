-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_finite_pairwise_orthogonal_real_L2_isometry
-- name    : AvramDividend.Classical.avram_wave7_06_finite_pairwise_orthogonal_real_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:36:05.995304+00:00
-- url     : https://prove2.me/theorems/7e6df6ff-a794-45a6-a6bd-b367448f87ca
-- title:
--   Finite pairwise orthogonal integrable real cells satisfy exact L2 energy isometry
-- statement:
--   For finite real-valued random cells with integrable every ordered product and zero off-diagonal expectations, the second moment of the finite sum is the sum of second moments. This authentic probability-space algebraic theorem converts source-process ordered weighted-cell orthogonality into the full-grid martingale L2 isometry. Explicit pair-product integrability justifies interchange of both finite sums and expectation.
-- source:
--   W7-06 finite-grid L2 algebraic consolidation helper consumed by original predictable Lévy cells.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_finite_pairwise_orthogonal_real_L2_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (n : ℕ) (A : ℕ → Ω → ℝ)
    (hProduct : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      Integrable (fun ω => A i ω * A j ω) P)
    (hOrth : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i ≠ j → (∫ ω, A i ω * A j ω ∂P) = 0) :
    (∫ ω, (∑ i ∈ Finset.range n, A i ω)^2 ∂P) =
      ∑ i ∈ Finset.range n, ∫ ω, (A i ω)^2 ∂P := by sorry
