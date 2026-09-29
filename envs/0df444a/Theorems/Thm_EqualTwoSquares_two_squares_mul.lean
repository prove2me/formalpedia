-- Prove2me | Theorems.Thm_EqualTwoSquares_two_squares_mul
-- name    : EqualTwoSquares.two_squares_mul
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-26T11:23:41.885183+00:00
-- url     : https://prove2.me/theorems/77049194-ce92-473d-81d3-9c2a18dfccf1
-- title:
--   Brahmagupta-Fibonacci identity, in both forms, over any commutative ring
-- statement:
--   For elements p, q, r and s of an arbitrary commutative ring, the product (p^2 + q^2)(r^2 + s^2) equals both (pr + qs)^2 + (ps - qr)^2 and (pr - qs)^2 + (ps + qr)^2.
-- source:
--   Classical identity (Brahmagupta; Fibonacci, Liber Quadratorum, 1225); machine-checked locally in examples/two-squares/Identity.lean.

import Mathlib

namespace EqualTwoSquares

/-- Brahmagupta–Fibonacci identity, both forms. -/
theorem two_squares_mul {R : Type*} [CommRing R] (p q r s : R) :
    (p^2 + q^2) * (r^2 + s^2) = (p * r + q * s)^2 + (p * s - q * r)^2 ∧
      (p^2 + q^2) * (r^2 + s^2) = (p * r - q * s)^2 + (p * s + q * r)^2 := by sorry

end EqualTwoSquares
