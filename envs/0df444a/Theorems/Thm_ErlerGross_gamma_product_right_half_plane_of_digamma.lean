-- Prove2me | Theorems.Thm_ErlerGross_gamma_product_right_half_plane_of_digamma
-- name    : ErlerGross.gamma_product_right_half_plane_of_digamma
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T20:30:38.525415+00:00
-- url     : https://prove2.me/theorems/2b436ef7-0abe-48a6-928e-45bafec7bfbf
-- title:
--   Gamma multiplication on the right half-plane from digamma
-- statement:
--   Assuming the digamma multiplication identity on the right half-plane, prove that the Gamma product has the expected multiplication form there, with a nonzero constant independent of the argument.

import Mathlib

namespace ErlerGross
theorem gamma_product_right_half_plane_of_digamma (n : Nat) (hn : 0 < n)
    (hpsi : forall z : Complex, 0 < z.re ->
      Finset.sum (Finset.range n) (fun k => Complex.digamma (z + (k : Complex) / n)) =
        n * Complex.digamma ((n : Complex) * z) - n * (Real.log n : Complex)) :
    Exists fun c : Complex => And (Not (c = 0)) (forall z : Complex, 0 < z.re ->
      Finset.prod (Finset.range n) (fun k => Complex.Gamma (z + (k : Complex) / n)) =
        c * Complex.exp (-(n : Complex) * z * (Real.log n : Complex)) *
          Complex.Gamma ((n : Complex) * z)) := by sorry
end ErlerGross
