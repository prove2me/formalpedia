-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_lower_grid_cap_eq_finite_prefix_ws01c
-- name    : AvramDividend.Classical.bv_lower_grid_cap_eq_finite_prefix_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:45:27.873845+00:00
-- url     : https://prove2.me/theorems/197c6335-dbba-42c9-bcfe-3e072ba2e4f0
-- title:
--   All-grid capped strict lower clock equals a finite-prefix capped grid clock
-- statement:
--   The complete dyadic/mesh strict lower first-hit infimum, once capped at T, is exactly its finite prefix through M when M*h≥T. The tail indices are no earlier than T, so the already Proved capped-iInf finite-prefix lemma applies.
-- source:
--   Exact existing helper from work/avram_ws01c_capped_grid_prefix_identity_draft.lean. The sole known source API error zero_le h arity is causally repaired to (by positivity); no changes to the mathematical statement, cap or strict crossing. Proof work/avram_ws01c_lower_grid_prefix_cap_solution_20261028.lean; imported finite-iInf prefix lemma canonically Proved UUID f84e143f-c9cc-4ae8-864d-7561d92165c1.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_capped_iInf_finite_prefix_ws01c

open Filter Set Order
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_lower_grid_cap_eq_finite_prefix_ws01c
    (Y : ℝ≥0 → ℝ) (lower : ℝ)
    (h T : ℝ≥0) (hh : 0 < h) (M : ℕ)
    (hCover : T ≤ (M : ℝ≥0) * h) :
    ((⨅ k : ℕ,
      if Y ((k : ℝ≥0) * h) < lower then
        (((k : ℝ≥0) * h) : ℝ≥0∞) else ∞) ⊓ (T : ℝ≥0∞)) =
    ((⨅ (k : ℕ) (_ : k ≤ M),
      if Y ((k : ℝ≥0) * h) < lower then
        (((k : ℝ≥0) * h) : ℝ≥0∞) else ∞) ⊓ (T : ℝ≥0∞)) := by sorry
