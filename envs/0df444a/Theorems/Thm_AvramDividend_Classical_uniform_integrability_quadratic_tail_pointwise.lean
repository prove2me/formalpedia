-- Prove2me | Theorems.Thm_AvramDividend_Classical_uniform_integrability_quadratic_tail_pointwise
-- name    : AvramDividend.Classical.uniform_integrability_quadratic_tail_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:37:40.415326+00:00
-- url     : https://prove2.me/theorems/9fd9b224-ac76-4992-afe6-2bdd040c5f6e
-- title:
--   Quadratic domination of the large-value tail of a nonnegative random variable
-- statement:
--   For a nonnegative real observation z and any positive truncation level R, the large-value part z·1_{z>R} is at most z²/R. If z≤R the left side is zero; if R<z, multiply by R and use z≥R and z≥0. This pointwise estimate yields E[Z·1_{Z>R}]≤E[Z²]/R for nonnegative random variables, which is the elementary uniform-integrability tail estimate in the L² proof that finite-grid stopped Lévy increment exponentials converge in expectation.
-- source:
--   Elementary Markov/second-moment tail inequality used in the bounded stopping-time approximation proof of the Lévy strong Markov property, Avram et al (2007), Proposition 1.

import Mathlib

theorem AvramDividend.Classical.uniform_integrability_quadratic_tail_pointwise
    (z R : ℝ) (hz : 0 ≤ z) (hR : 0 < R) :
    (if R < z then z else 0) ≤ z ^ 2 / R := by sorry
