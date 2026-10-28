-- Prove2me | Theorems.Thm_D1Bound5_all_large_overlap_constants
-- name    : D1Bound5.all_large_overlap_constants
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:07:10.611812+00:00
-- url     : https://prove2.me/theorems/6cf4f303-1a95-4312-8420-63565fb606cd
-- title:
--   All large overlap constants
-- statement:
--   All fifteen sufficient overlap quotients in the no-small-entry branch, followed by the ordinary-tail ratio. The order is precisely Table pr-overlaps of the manuscript. Expressions are written as a positive rational coefficient times a monomial so that monotonicity in A,B,S is explicit. No tuple growth, interval exclusion, or main theorem is assumed in this numerical certificate.
-- source:
--   D1Bound5/AllLargeOverlapConstants.lean, lines 19-74, SHA-256 1ecfa6ec2be53bcc4be16c181743e15299183cf147454f6adf4697f119eaefb4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

section
namespace D1Bound5




theorem _root_.D1Bound5.all_large_overlap_constants
    (A B S : ℝ) (hA : 3 ≤ A) (hB : 3 ≤ B) (hS : 3 ≤ S) :
    (13 / 10 : ℝ) <
      (1024 * (1 - 1 / 4000) / 12100) * (A ^ 10 * B ^ 10 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (256 / (36 * 243 ^ 2 * (4001 / 3999))) * (A ^ 8 * B ^ 0 * S ^ 4) ∧
    (13 / 10 : ℝ) <
      (400 ^ 2 / (16 * (5 / 4) ^ 2 * 2400 ^ 2 * (4001 / 3999))) *
        (A ^ 20 * B ^ 4 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (400 ^ 2 / (16 * (5 / 4) ^ 2 * 2400 ^ 2 * (4001 / 3999))) *
        (A ^ 20 * B ^ 0 * S ^ 2) ∧
    (13 / 10 : ℝ) <
      (400 ^ 2 / (16 * 3 ^ 2 * 4143 ^ 2 * (4001 / 3999))) *
        (A ^ 20 * B ^ 0 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (400 ^ 2 / (16 * 3 ^ 2 * 2265 ^ 2 * (4001 / 3999))) *
        (A ^ 20 * B ^ 0 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (400 ^ 4 / (16 * (35 / 16) ^ 2 * ((8 / 9) * 608 ^ 2) ^ 2 * (4001 / 3999))) *
        (A ^ 36 * B ^ 0 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (400 ^ 4 / (16 * (3920 / 81) ^ 2 * 4143 ^ 2 * (4001 / 3999))) *
        (A ^ 34 * B ^ 2 * S ^ 2) ∧
    (13 / 10 : ℝ) <
      (400 ^ 2 / (16 * (35 / 32) ^ 2 * 165763 ^ 2 * (4001 / 3999))) *
        (A ^ 22 * B ^ 4 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (400 ^ 4 / (16 * (35 / 32) ^ 2 * 4143 ^ 2 * (4001 / 3999))) *
        (A ^ 36 * B ^ 8 * S ^ 0) ∧
    (7 / 5 : ℝ) <
      ((400 / (35 / 32)) ^ 2 / (16 * 165763 ^ 2 * (4001 / 3999))) *
        (A ^ 14 * B ^ 0 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (400 ^ 4 / (144 * (63 / 8) ^ 2 * 42 ^ 8 * (4001 / 3999))) *
        (A ^ 38 * B ^ 2 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (400 ^ 4 / (4 * 3113013 ^ 2 * (5 / 2) ^ 8 * (4001 / 3999))) *
        (A ^ 36 * B ^ 0 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (400 ^ 6 / (144 * (495 / 64) ^ 2 * 42 ^ 10 * (4001 / 3999))) *
        (A ^ 54 * B ^ 10 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (400 ^ 6 / (36 * 42 ^ 12 * (5 / 2) ^ 10 * (4001 / 3999))) *
        (A ^ 52 * B ^ 4 * S ^ 0) ∧
    (13 / 10 : ℝ) < (400 / 105) * (A ^ 8 * B ^ 1 * S ^ 3) := by sorry





end D1Bound5
end
