-- Prove2me | Theorems.Thm_FamousTheorems_issolvable_gal_minpoly
-- name    : FamousTheorems.issolvable_gal_minpoly
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:40.83926+00:00
-- url     : https://prove2.me/theorems/495f8caa-5af6-404e-9226-f63921c45c55
-- title:
--   Solvability by radicals implies solvable Galois group
-- statement:
--   **One direction of the Abel\u2013Ruffini theorem.** If an element is expressible by radicals over a field, then the Galois group of its minimal polynomial is solvable. Each radical extension adjoins an $n$-th root, which contributes an abelian layer to the Galois group; stacking finitely many such layers produces a solvable group. Reading the implication backwards gives the classical impossibility result: a polynomial whose Galois group is not solvable — $S_5$, for instance, realised by $x^5 - 4x + 2$ — cannot be solved by radicals, so there is no quintic formula. Ruffini gave an incomplete argument in 1799 and Abel a complete one in 1824; Galois supplied the group-theoretic explanation that makes the statement an equivalence. **Formalization note.** `IsSolvableByRad` is the closure of the base field under radicals, and `minpoly` the minimal polynomial. The result is Mathlib's `isSolvable_gal_minpoly`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem issolvable_gal_minpoly :
    ∀ {F : Type u_1} {E : Type u_2} [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] 
    {x : E}, x ∈ solvableByRad F E → Group.IsSolvable (minpoly F x).Gal := by sorry

end FamousTheorems
