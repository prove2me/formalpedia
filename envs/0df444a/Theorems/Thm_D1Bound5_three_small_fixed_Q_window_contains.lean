-- Prove2me | Theorems.Thm_D1Bound5_three_small_fixed_Q_window_contains
-- name    : D1Bound5.three_small_fixed_Q_window_contains
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T21:42:46.863649+00:00
-- url     : https://prove2.me/theorems/205db1a3-acc8-4807-99c0-7e66dff97e49
-- title:
--   A simpler interval lies inside the fixed-extension Q window
-- statement:
--   For every positive real number $C$,
--   $$\frac{4\cdot55^2\cdot85^6C^3}{1-1/4000}\le10^{38}C^3,$$
--   $$\frac{C^7}{10^{29}}\le\frac{C^7}{9\cdot85^2(1+1/4000)}.$$
--   These numerical comparisons locate the simpler endpoints inside the Q window.
-- source:
--   D1Bound5/ThreeSmallFixedScalar.lean, D1Bound5.three_small_fixed_Q_window_contains, lines 118-125; original file SHA-256 d59d2ffa2f67d68b2084d696be49c307e1d6ca76bebadcdcb67883e86b4bbd55. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic

theorem D1Bound5.three_small_fixed_Q_window_contains (C : ℝ) (hC : 0 < C) :
    4*55^2*85^6*C^3/(1-1/4000 : ℝ) ≤ (10 : ℝ)^38*C^3 ∧
      C^7/(10 : ℝ)^29 ≤ C^7/(9*85^2*(1+1/4000 : ℝ)) := by sorry
