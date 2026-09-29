-- Prove2me | solution 1 for norm_X_mult_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T06:34:06.976731+00:00
-- url     : https://prove2.me/submissions/00e5cb03-a743-42ed-bc20-b0a2940f67f0

import Mathlib
import Definitions.Def_timepiece_corrector
import Theorems.Thm_norm_X_mult_list_eq_one
open Complex Finset Filter Topology
open scoped ArithmeticFunction ArithmeticFunction.Moebius ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (n P : ℕ) (ω : Ω_infty) : ‖X_mult n P ω‖ = 1 := by
  unfold X_mult
  exact norm_X_mult_list_eq_one P ω (Nat.primeFactorsList n)
