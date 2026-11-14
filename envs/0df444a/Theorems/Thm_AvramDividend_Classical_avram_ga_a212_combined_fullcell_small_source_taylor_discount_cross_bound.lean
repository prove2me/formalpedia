-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a212_combined_fullcell_small_source_taylor_discount_cross_bound
-- name    : AvramDividend.Classical.avram_ga_a212_combined_fullcell_small_source_taylor_discount_cross_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:15:47.91775+00:00
-- url     : https://prove2.me/theorems/8a09ad83-1dc8-4a28-bb25-0eb9aa6f2b61
-- title:
--   Combined Gaussian full-cell small-step positive residual bounded by Taylor, discount-width and Hessian cross energies
-- statement:
--   On a true small Gaussian source cell, a bound on the classical Taylor remainder, a local Lipschitz bound for the original value change, a bound on the discount difference and a compact Hessian bound imply a one-sided upper bound for the positive combined zero-jump residual. The upper bound is epsilon times raw squared increment, plus discount width times local Lipschitz times raw absolute increment, plus compact Hessian times the raw-centred quadratic cross magnitude. This source-preserving cancellation allows proving a134 without extracting the potentially nonintegrable arbitrary value discount component a151.
-- source:
--   Exact original Gaussian combined source small-step algebra and absolute inequalities.

import Mathlib

theorem AvramDividend.Classical.avram_ga_a212_combined_fullcell_small_source_taylor_discount_cross_bound (e0 e1 u v d h r z ε Q L M : ℝ)
 (he0 : 0 ≤ e0) (he0one : e0 ≤ 1)
 (hε : 0 ≤ ε) (hQ : 0 ≤ Q) (hL : 0 ≤ L) (hM : 0 ≤ M)
 (hTaylor : |v-u-d*r-h/2*r^2| ≤ ε*r^2)
 (hDisc : |e1-e0| ≤ Q)
 (hLip : |v-u| ≤ L*|r|) (hh : |h| ≤ M) :
 max (e1*(v-u)-e0*(d*r+h/2*z^2)) 0 ≤
   ε*r^2 + Q*L*|r| + M/2*|r^2-z^2| := by sorry
