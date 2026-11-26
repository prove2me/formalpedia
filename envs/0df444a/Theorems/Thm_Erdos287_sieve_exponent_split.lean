-- Prove2me | Theorems.Thm_Erdos287_sieve_exponent_split
-- name    : Erdos287.sieve_exponent_split
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T04:32:51.041499+00:00
-- url     : https://prove2.me/theorems/793fd95d-7313-5737-87fc-4620db027af9
-- title:
--   Compatible Type II and Type III ranges near exponent seven thirteenths
-- statement:
--   Set D=7/13−ε, where 0<ε≤1/10000, and let 1/13≤ν≤1/4. A cutoff 3D−1−ν+ε separates the range where the Type II diagonal is small from a lower range in which all three Type III inequalities hold for a separate factorization of the same level D.
-- source:
--   Erdős Problem #287, exponent analysis for the mixed-residue sieve. Type II and Type III exponent functions are from Sections 5 and 8 of Zongkun Zheng, Primes in simultaneous arithmetic progressions, arXiv:2512.22798.

import Mathlib

theorem Erdos287.sieve_exponent_split (ε ν : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10000)
    (hν : 1 / 13 ≤ ν) (hν' : ν ≤ 1 / 4) :
    let level := 7 / 13 - ε
    let cutoff := 3 * level - 1 - ν + ε
    let upperS := cutoff + 2 * (level - 1) / 3
    (0 < upperS ∧ upperS < level) ∧
    (∀ r s : ℝ, r ≤ level - ν + ε / 12 → cutoff ≤ r + s →
      r - s / 2 + ν ≤ 1 / 2 - ε / 4) ∧
    (∀ r s : ℝ, r ≤ level - upperS → s ≤ upperS → r + s ≤ cutoff →
      4 * r + 3 * s - 1 ≤ 1 - ν - ε ∧
      7 * r / 4 + 3 * s / 2 ≤ 1 - ν - ε ∧
      3 * r / 2 + 2 * s ≤ 1 - ν - ε) := by sorry
