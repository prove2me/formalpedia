-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB95_product_refinement_endpoint_equalities
-- name    : AvramDividend.Classical.avram_gbB95_product_refinement_endpoint_equalities
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:56:40.451736+00:00
-- url     : https://prove2.me/theorems/61fbde64-10e3-4609-8c68-6181935311ac
-- title:
--   Exact original coarse and product-refinement endpoint identities
-- statement:
--   For original finite uniform horizons n and coarse size m+1 refined by a positive integer factor b, both endpoints of each coarse cell agree algebraically with the corresponding product-grid endpoints. These identities combine with the Proved indicator telescoping lemma B94 to prove B93 and the source-exact finite-step time energy B82.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB95_product_refinement_endpoint_equalities
    (n m b i : ℕ) (hn : 0 < n) (hb : 0 < b) :
    let D : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let δ : ℝ := (n : ℝ) / (((m + 1) * b : ℕ) : ℝ)
    ((((i : ℝ≥0) * D) : ℝ) = ((i * b : ℕ) : ℝ) * δ) ∧
    (((((i : ℝ≥0) * D) + D : ℝ≥0) : ℝ) =
      ((i * b + b : ℕ) : ℝ) * δ) := by sorry
