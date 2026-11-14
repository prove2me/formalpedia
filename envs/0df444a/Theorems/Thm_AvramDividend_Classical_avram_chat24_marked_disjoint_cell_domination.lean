-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_marked_disjoint_cell_domination
-- name    : AvramDividend.Classical.avram_chat24_marked_disjoint_cell_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:19:15.330497+00:00
-- url     : https://prove2.me/theorems/12301111-c50b-418a-9145-8d34f7617be0
-- title:
--   Disjoint bounded cells dominate marked finite sums
-- statement:
--   Independent measure-theoretic finite-step estimate extracted mathematically from the complete proof of parent 1eea7159-587a-416f-ae50-9a71b706b90c. A bounded scalar coefficient on pairwise disjoint ordered cells yields a measurable step with norm <=C. Multiply by the negative mark. The support predicate ensures positive time and negative mark; beyond B all cells vanish by hcap. This lemma requires no path, jump limits, integrability or original parent. The accepted scalar disjoint-cell step theorem supplies the scalar bound.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_chat24_marked_disjoint_cell_domination
    (μ : Measure (ℝ≥0 × ℝ)) (B : ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (hu : ∀ n, StrictMono (u n))
    (hcap : ∀ n i, i ∈ Finset.range (n + 1) → u n (i + 1) ≤ B)
    (c : ℕ → ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (n0 : ℕ)
    (hc : ∀ n, n0 ≤ n → ∀ i ∈ Finset.range (n + 1), ‖c n i‖ ≤ C)
    (hsupport : ∀ᵐ p ∂μ, 0 < p.1 ∧ p.2 < 0) :
    let F : ℕ → ℝ≥0 × ℝ → ℝ := fun n p => if n0 ≤ n then
      ∑ i ∈ Finset.range (n + 1),
        if u n i < p.1 ∧ p.1 ≤ u n (i + 1) then c n i * (-p.2) else 0
      else 0
    let D : ℝ≥0 × ℝ → ℝ := fun p =>
      if 0 < p.1 ∧ p.1 ≤ B ∧ p.2 < 0 then C * (-p.2) else 0
    (∀ n, AEStronglyMeasurable (F n) μ) ∧
      (∀ n, ∀ᵐ p ∂μ, ‖F n p‖ ≤ D p) := by sorry
