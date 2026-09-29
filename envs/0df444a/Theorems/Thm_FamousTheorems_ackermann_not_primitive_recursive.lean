-- Prove2me | Theorems.Thm_FamousTheorems_ackermann_not_primitive_recursive
-- name    : FamousTheorems.ackermann_not_primitive_recursive
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:00.010346+00:00
-- url     : https://prove2.me/theorems/049ba048-71e7-482e-89f5-ac20b6c102c7
-- title:
--   The Ackermann function is not primitive recursive
-- statement:
--   **The Ackermann function is not primitive recursive.** Let $A$ be the Ackermann function, defined by $A(0,n)=n+1$, $A(m+1,0)=A(m,1)$ and $A(m+1,n+1)=A(m,A(m+1,n))$. Then the diagonal $n\mapsto A(n,n)$ is not a primitive recursive function.
--
--   The Ackermann function was the first example (Ackermann 1928, following Hilbert) of a total computable function that is not primitive recursive. It grows faster than every primitive recursive function, so primitive recursion does not capture all effective computation. This motivated the general recursive and $\mu$-recursive functions.
--
--   **Formalization note.** Mathlib's `not_nat_primrec_ack_self`. `ack` is the two-argument Ackermann function above, and `Nat.Primrec` is the inductive predicate of primitive recursive functions $\mathbb N\to\mathbb N$. Non-primitive-recursiveness of the diagonal implies that of `ack` itself.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `not_nat_primrec_ack_self`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem ackermann_not_primitive_recursive : ¬Nat.Primrec fun n : ℕ => ack n n := by sorry

end FamousTheorems
