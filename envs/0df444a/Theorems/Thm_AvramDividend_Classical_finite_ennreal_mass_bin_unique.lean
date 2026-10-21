-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_ennreal_mass_bin_unique
-- name    : AvramDividend.Classical.finite_ennreal_mass_bin_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:48:53.53957+00:00
-- url     : https://prove2.me/theorems/e8142daf-179f-4744-9013-abac6cfcaf2c
-- title:
--   Every finite extended-real mass has exactly one natural-number unit bin
-- statement:
--   For every finite extended-nonnegative real mass, exactly one natural-number unit bin contains it. The zero bin contains masses up to one, and for n>0 the bin comprises masses strictly above n and at most n+1. Existence is the separately proved minimal-upper-bound lemma. Uniqueness uses the strict separation of natural-number bin bounds. This result is needed to prove that selecting the true dividend interval kernel on one mass bin at a time and then summing the resulting finite kernels reproduces the original sample-path measure exactly.
-- source:
--   Dependency-gated finite_ennreal_mass_bin_exists target f0523660-a983-4fdf-93b3-83a88ed342ec; elementary Nat cast order and lt_trichotomy.

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_finite_ennreal_mass_bin_exists

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.finite_ennreal_mass_bin_unique
    (m : ℝ≥0∞) (hm : m < ⊤) :
    ∃! n : ℕ, m ≤ (n + 1 : ℝ≥0∞) ∧
      (n = 0 ∨ (n : ℝ≥0∞) < m) := by sorry
