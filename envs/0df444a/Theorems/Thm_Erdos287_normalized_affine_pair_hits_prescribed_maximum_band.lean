-- Prove2me | Theorems.Thm_Erdos287_normalized_affine_pair_hits_prescribed_maximum_band
-- name    : Erdos287.normalized_affine_pair_hits_prescribed_maximum_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T08:05:25.588873+00:00
-- url     : https://prove2.me/theorems/d08b7075-bdc3-4e38-95a3-c9714340f227
-- title:
--   Normalized compatible prime forms place their adjacent multiples in a prescribed band
-- statement:
--   Let $a<b$ with $b-a\mid a$, and set $c=a/(b-a)$. Suppose $M,V,d$ are positive and the normalized parameters satisfy
--   \[
--    (49/50)V/M\le d\le(51/50)V/M,\quad
--    (4/9)V\le Qt\le(9/10)V,\quad
--    (999/1000)Q/d\le cb\le(101/100)Q/d,\quad
--    c+1\le M/100.
--   \]
--   Then there is an $x$ with $x+1\le M<e x$ such that $bt+1$ divides $x$ and $at+1$ divides $x+1$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Exact arithmetic placement for the hierarchical slope construction.

import Mathlib

theorem Erdos287.normalized_affine_pair_hits_prescribed_maximum_band (a b t M : ℕ) (Q d V : ℝ)
    (hM : 0 < M) (hab : a < b) (hdiv : (b - a) ∣ a)
    (hd : 0 < d) (hV : 0 < V)
    (hdlo : (49 / 50 : ℝ) * V / M ≤ d)
    (hdhi : d ≤ (51 / 50 : ℝ) * V / M)
    (htlo : (4 / 9 : ℝ) * V ≤ Q * t)
    (hthi : Q * t ≤ (9 / 10 : ℝ) * V)
    (hcoeflo : (999 / 1000 : ℝ) * Q / d ≤ ((a / (b - a) : ℕ) : ℝ) * b)
    (hcoefhi : ((a / (b - a) : ℕ) : ℝ) * b ≤ (101 / 100 : ℝ) * Q / d)
    (herror : ((a / (b - a) + 1 : ℕ) : ℝ) ≤ (M : ℝ) / 100) :
    ∃ x : ℕ, (b * t + 1) ∣ x ∧ (a * t + 1) ∣ (x + 1) ∧
      x + 1 ≤ M ∧ (M : ℝ) < Real.exp 1 * x := by sorry
