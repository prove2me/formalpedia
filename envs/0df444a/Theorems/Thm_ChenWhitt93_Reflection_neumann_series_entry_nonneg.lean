-- Prove2me | Theorems.Thm_ChenWhitt93_Reflection_neumann_series_entry_nonneg
-- name    : ChenWhitt93.Reflection.neumann_series_entry_nonneg
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-01T09:39:01.885573+00:00
-- url     : https://prove2.me/theorems/00bc7dbe-e304-43c0-b5b5-01325fb693f4
-- title:
--   Entrywise nonnegativity of the matrix Neumann series
-- statement:
--   An entrywise-nonnegative real matrix with summable powers has an entrywise-nonnegative Neumann series sum.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), nonnegativity of (I-Q)^{-1} used in Eq. (2.9), p. 339

import Mathlib

open Filter Topology Matrix

namespace ChenWhitt93.Reflection

/-- An entrywise-nonnegative matrix with summable powers has an entrywise-
nonnegative Neumann series sum (feeds the componentwise bound (2.9) via
`(I - Q)^{-1} = sum Q^k >= 0`). -/
theorem neumann_series_entry_nonneg {n : Nat} (Q : Matrix (Fin n) (Fin n) Real)
    (hQ : forall i j, 0 <= Q i j) (hsum : Summable (fun k : Nat => Q ^ k)) :
    forall i j, 0 <= (tsum fun k : Nat => Q ^ k) i j := by sorry

end ChenWhitt93.Reflection
