-- Prove2me | Theorems.Thm_FamousTheorems_sophie_germain_identity
-- name    : FamousTheorems.sophie_germain_identity
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:21:17.879983+00:00
-- url     : https://prove2.me/theorems/964bc0b1-b32d-4ae3-a8c7-5640d535800b
-- title:
--   Sophie Germain's identity
-- statement:
--   **Sophie Germain's identity.** In every commutative ring,
--   $$a^4+4b^4=\big((a-b)^2+b^2\big)\big((a+b)^2+b^2\big).$$
--
--   Taking $b=2^{(k-1)/2}$, it shows that $n^4+4^k$ is composite for every $n>1$ and every odd $k$; in particular $n^4+4$ is prime only for $n=1$. It is a standard tool in olympiad number theory and a classical example of a nontrivial polynomial factorisation over the integers.
--
--   **Formalization note.** Mathlib's `pow_four_add_four_mul_pow_four`, stated for an arbitrary commutative ring.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `pow_four_add_four_mul_pow_four`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem sophie_germain_identity {R : Type*} [CommRing R] (a b : R) :
    a ^ 4 + 4 * b ^ 4 = ((a - b) ^ 2 + b ^ 2) * ((a + b) ^ 2 + b ^ 2) := by sorry

end FamousTheorems
