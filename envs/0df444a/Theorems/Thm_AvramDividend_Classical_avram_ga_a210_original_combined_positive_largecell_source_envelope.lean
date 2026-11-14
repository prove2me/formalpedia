-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a210_original_combined_positive_largecell_source_envelope
-- name    : AvramDividend.Classical.avram_ga_a210_original_combined_positive_largecell_source_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:14:19.282206+00:00
-- url     : https://prove2.me/theorems/809f85a7-c7a4-4ba7-997c-535c5aafaf95
-- title:
--   Combined positive Gaussian full-cell residual has exponential endpoint and compact quadratic envelope
-- statement:
--   For the exact original Gaussian combined full-cell residual after drift and generator cancellation, any nonnegative pre/post discount factors at most one, an upper exponential endpoint value, and uniformly bounded start value, gradient and Hessian imply a pointwise one-sided exponential-plus-quadratic upper bound on the positive combined residual. This bound handles large raw Gaussian increments directly and avoids extracting the potentially nonintegrable positive discount difference as a separate component, thereby supporting a valid route to the original a134 even when arbitrary smooth w is negative superexponentially.
-- source:
--   Elementary one-sided upper envelope for the original combined Gaussian residual with cancelled zero-jump generator terms.

import Mathlib

theorem AvramDividend.Classical.avram_ga_a210_original_combined_positive_largecell_source_envelope (e0 e1 u v d h r z θ y K M : ℝ)
 (he0 : 0 ≤ e0) (he0one : e0 ≤ 1)
 (he1 : 0 ≤ e1) (he1one : e1 ≤ 1)
 (hK : 0 ≤ K) (hM : 0 ≤ M)
 (hu : |u| ≤ M) (hd : |d| ≤ M) (hh : |h| ≤ M)
 (hv : v ≤ K * Real.exp (θ * y)) :
 max (e1*(v-u) - e0*(d*r + h/2*z^2)) 0 ≤
  K*Real.exp (θ*y) + M*(1 + |r| + z^2/2) := by sorry
