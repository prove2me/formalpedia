-- Prove2me | Theorems.Thm_BranchSpectral_nonnegative_via_branches
-- name    : BranchSpectral.nonnegative_via_branches
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T05:51:09.622349+00:00
-- url     : https://prove2.me/theorems/74e9cefb-0c73-4088-9215-2155bfad6b1b
-- title:
--   Nonnegativity from the empty finite and infinite alternatives
-- statement:
--   Let Qₙ(u) be real and O⊆ℕ. Let N mean that some n≥1,u>0 has Qₙ(u)<0. Assume O=∅ implies Qₙ(u)≥0 for all n≥1,u>0, that N is incompatible with finite nonempty O, and that N is incompatible with infinite O. Then
--   $$Q_n(u)\ge0\quad(n\ge1,\ u>0).$$
--   This is a logical closure lemma; the two incompatibilities are hypotheses here.
--   Scope: the explicit hypotheses of this theorem only. No proof of RH or of higher tower-diagonal positivity is claimed.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Conditional Branch 2/3 certificate, 16 Nov 2026. No claim of novelty.

import Mathlib
open MeasureTheory Set Filter Topology

theorem BranchSpectral.nonnegative_via_branches (Q : ℕ → ℝ → ℝ) (off : Set ℕ)
    (hRH : off = ∅ → ∀ n ≥ 1, ∀ u > 0, 0 ≤ Q n u)
    (b2 : ¬ ((∃ n ≥ 1, ∃ u > 0, Q n u < 0) ∧ off.Finite ∧ off.Nonempty))
    (b3 : ¬ ((∃ n ≥ 1, ∃ u > 0, Q n u < 0) ∧ off.Infinite)) :
    ∀ n ≥ 1, ∀ u > 0, 0 ≤ Q n u := by sorry
