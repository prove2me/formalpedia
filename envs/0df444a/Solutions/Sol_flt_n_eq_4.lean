-- Prove2me | solution 1 for flt_n_eq_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-11T08:27:58.295274+00:00
-- url     : https://prove2.me/submissions/6a15b23c-fd0b-469b-ab98-91ee50a34b61

import Mathlib.NumberTheory.FLT.Four
import Mathlib.Data.Nat.Basic

-- fermatLastTheoremFour expects (a ≠ 0) not (0 < a); convert via omega.

theorem solution
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 4 + b ^ 4 ≠ c ^ 4 :=
  fermatLastTheoremFour a b c (by omega) (by omega) (by omega)
