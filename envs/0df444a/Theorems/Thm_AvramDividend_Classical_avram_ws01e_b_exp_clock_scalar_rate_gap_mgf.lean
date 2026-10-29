-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_exp_clock_scalar_rate_gap_mgf
-- name    : AvramDividend.Classical.avram_ws01e_b_exp_clock_scalar_rate_gap_mgf
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T20:43:43.372441+00:00
-- url     : https://prove2.me/theorems/a63b0a47-ee0a-45f0-8a1e-51dcda707317
-- title:
--   Exact exponential-clock scalar moment at every positive rate gap
-- statement:
--   For the actual exponential probability measure Exp(p), every real exponent a strictly below its positive rate p has the exact nonnegative extended-real moment p/(p−a), expressed without division as ofReal(p−a) times the exponential-PDF lintegral = ofReal p. This covers negative a and p−a>0, with the real clock restricted to its nonnegative part. It supplies the genuine integrable clock factor for the Esscher random-terminal moment without imposing an unwarranted sign on the shifted Lévy exponent.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2013) §2.1 exponential clock resolvent; accepted chat04_actual_exp_clock_terminal_moment_rate_identity_ws01a 3281a368, algebraic scalar rate calculation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_exp_clock_scalar_rate_gap_mgf
    (p a : ℝ) (hp : 0 < p) (ha : a < p) :
    ENNReal.ofReal (p - a) *
      (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF p t *
        ENNReal.ofReal (Real.exp ((Real.toNNReal t : ℝ) * a)) ∂volume) =
      ENNReal.ofReal p := by sorry
