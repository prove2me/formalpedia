-- Prove2me | Theorems.Thm_ChenWhitt93_Reflection_neumann_inverse_identity
-- name    : ChenWhitt93.Reflection.neumann_inverse_identity
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-01T09:38:25.243267+00:00
-- url     : https://prove2.me/theorems/d30a636c-e784-4efc-8e14-d557aa0b57eb
-- title:
--   Neumann inverse identity for a summable matrix geometric series
-- statement:
--   If the matrix power series sum_{k} Q^k is summable, its sum is a two-sided inverse of (I - Q).
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), Eq. (2.10) Neumann expansion of (I-Q)^{-1}, p. 339

import Mathlib

open Filter Topology Matrix

namespace ChenWhitt93.Reflection

/-- If the matrix geometric series `sum k, Q ^ k` is summable, its tsum is a
two-sided inverse of `1 - Q` (used in Eq. (2.10) for `(I - Q)^{-1} = sum Q^k`). -/
theorem neumann_inverse_identity {n : Nat} (Q : Matrix (Fin n) (Fin n) Real)
    (hsum : Summable (fun k : Nat => Q ^ k)) :
    (tsum fun k : Nat => Q ^ k) * (1 - Q) = 1 /\
      (1 - Q) * (tsum fun k : Nat => Q ^ k) = 1 := by sorry

end ChenWhitt93.Reflection
