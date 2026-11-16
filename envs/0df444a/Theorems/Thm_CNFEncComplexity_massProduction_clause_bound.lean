-- Prove2me | Theorems.Thm_CNFEncComplexity_massProduction_clause_bound
-- name    : CNFEncComplexity.massProduction_clause_bound
-- status  : Proved
-- author  : @bersubs
-- created : 2026-11-15T06:43:10.853661+00:00
-- url     : https://prove2.me/theorems/b05bf85d-c53f-4554-8a9a-6431e74f3d6f
-- title:
--   Clause bound for mass-production CNF assembly
-- statement:
--   A linear number of sparse slot encodings with a bounded total support size, together with a checker of polynomial cost per query, has the shifted square-root polylogarithmic clause bound of Lemma 11.
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614, Lemma 11, Section 3.4.

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open scoped BigOperators

theorem CNFEncComplexity.massProduction_clause_bound (A D H e j : ℕ) :
    ∃ C K : ℕ, ∀ n b q d : ℕ, 1 ≤ b → b ≤ 2 ^ n → q ≤ 16 * b →
      (d : ℝ) ≤ (D : ℝ) * ((n : ℝ) + 1) ^ e →
      ∀ deg clauses : Fin q → ℕ, (∑ r, deg r) ≤ 2 ^ n * d →
      (∀ r, (clauses r : ℝ) ≤ (A : ℝ) * ((n : ℝ) + 1 + Real.sqrt ((n : ℝ) * deg r))) →
      ∀ checker : ℕ, (checker : ℝ) ≤ (H : ℝ) * (b : ℝ) * ((n : ℝ) + 1) ^ j →
      ((∑ r, clauses r : ℕ) : ℝ) + checker ≤
        (C : ℝ) * (Real.sqrt ((2 : ℝ) ^ n * b) + 1) *
          Real.logb 2 (Real.sqrt ((2 : ℝ) ^ n * b) + 2) ^ K := by sorry
