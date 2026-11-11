-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger56_discounted_gaussian_characteristic_roots
-- name    : AvramDividend.Classical.avram_gledger56_discounted_gaussian_characteristic_roots
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T23:47:02.25229+00:00
-- url     : https://prove2.me/theorems/9f046cfa-46b3-4345-82a7-b203cd9265a9
-- title:
--   Positive and negative real characteristic roots for the discounted Gaussian generator
-- statement:
--   For a positive Gaussian variance a and positive discount q, the quadratic Gaussian characteristic equation has one positive and one negative real root. Their sum and product give the exact factorisation b=-a(r+l), q=-arl required to turn the original zero-jump HJB into the first-order integrating-factor inequality in gledger55. This is independent of the stochastic process, strategy and any smoothness assumptions.
-- source:
--   Necessary elementary characteristic-root prerequisite for gledger55 and the one-sided HJB exponential spatial envelope in Open gledger53 (a604fe09).

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_gledger56_discounted_gaussian_characteristic_roots
    (a b q : ℝ) (ha : 0 < a) (hq : 0 < q) :
    ∃ r l : ℝ, 0 < r ∧ l < 0 ∧
      b = -a * (r + l) ∧ q = -a * r * l := by sorry
