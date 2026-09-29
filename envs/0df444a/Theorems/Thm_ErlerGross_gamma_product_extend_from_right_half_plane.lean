-- Prove2me | Theorems.Thm_ErlerGross_gamma_product_extend_from_right_half_plane
-- name    : ErlerGross.gamma_product_extend_from_right_half_plane
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T20:31:40.24699+00:00
-- url     : https://prove2.me/theorems/f4a3ef0e-cf6f-4c6f-8160-de80748fdf98
-- title:
--   Extend the Gamma product formula to all complex arguments
-- statement:
--   Let n be a positive integer and c a nonzero complex constant. If the Gamma multiplication identity with constant c holds for all z with positive real part, then it holds for all complex z. This is the continuation step from the right half-plane.

import Mathlib

namespace ErlerGross
theorem gamma_product_extend_from_right_half_plane (n : Nat) (hn : 0 < n)
    (c : Complex) (hc : Not (c = 0))
    (hpos : forall z : Complex, 0 < z.re ->
      Finset.prod (Finset.range n) (fun k => Complex.Gamma (z + (k : Complex) / n)) =
        c * Complex.exp (-(n : Complex) * z * (Real.log n : Complex)) *
          Complex.Gamma ((n : Complex) * z)) :
    forall z : Complex,
      Finset.prod (Finset.range n) (fun k => Complex.Gamma (z + (k : Complex) / n)) =
        c * Complex.exp (-(n : Complex) * z * (Real.log n : Complex)) *
          Complex.Gamma ((n : Complex) * z) := by sorry
end ErlerGross
