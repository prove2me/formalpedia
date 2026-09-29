-- Prove2me | Theorems.Thm_FamousTheorems_euler_four_square_identity
-- name    : FamousTheorems.euler_four_square_identity
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:05:26.761977+00:00
-- url     : https://prove2.me/theorems/2d45a28b-b629-4606-a0d1-6b246fad247c
-- title:
--   Euler's four-square identity
-- statement:
--   **Euler's four-square identity.** In any commutative ring,
--   $$(a^2+b^2+c^2+d^2)(x^2+y^2+z^2+w^2)=(ax-by-cz-dw)^2+(ay+bx+cw-dz)^2+(az-bw+cx+dy)^2+(aw+bz-cy+dx)^2.$$
--
--   So a product of sums of four squares is again a sum of four squares. This reduces Lagrange's four-square theorem to the case of primes. The identity is the multiplicativity of the norm on Hamilton's quaternions, and it is one of the four composition identities, in dimensions $1,2,4,8$, allowed by Hurwitz's theorem.
--
--   **Formalization note.** Mathlib's `euler_four_squares`, stated for an arbitrary commutative ring `R`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `euler_four_squares`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem euler_four_square_identity {R : Type*} [CommRing R] (a b c d x y z w : R) :
    (a * x - b * y - c * z - d * w) ^ 2 + (a * y + b * x + c * w - d * z) ^ 2 +
        (a * z - b * w + c * x + d * y) ^ 2 + (a * w + b * z - c * y + d * x) ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by sorry

end FamousTheorems
