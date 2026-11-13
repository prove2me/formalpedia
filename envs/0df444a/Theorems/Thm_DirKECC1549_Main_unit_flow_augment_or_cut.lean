-- Prove2me | Theorems.Thm_DirKECC1549_Main_unit_flow_augment_or_cut
-- name    : DirKECC1549.Main.unit_flow_augment_or_cut
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-12T10:36:01.051197+00:00
-- url     : https://prove2.me/theorems/dd03d34a-13ab-4493-a33c-406fa860e54f
-- title:
--   Integral unit flow: augment or exhibit an equal cut
-- statement:
--   Let $D$ be a finite directed multigraph with distinct vertices $u,v$, and let $F$ be the support of an integral unit-capacity $u$–$v$ flow of value $q$. Then either there is an integral unit-capacity $u$–$v$ flow of value $q+1$, or there is a vertex set $S$ with $u\in S$, $v\notin S$, and exactly $q$ outgoing edges.
--
--   This is the augmentation-or-cut alternative underlying the Ford–Fulkerson proof. Edge identifiers distinguish parallel edges, and loops are allowed.
-- source:
--   Derived step in Ford–Fulkerson, Flows in Networks (1962), Chapter I, Section 5, Theorem 5.1 p.19, for the mission’s integral unit-flow encoding; see also Georgiadis et al., STOC 2027 submission #1549, Section 2 p.9.

import Definitions.Def_DirKECC1549_Main_Alg3
set_option autoImplicit false

namespace DirKECC1549.Main

theorem unit_flow_augment_or_cut {n m : ℕ} (D : Fin m → Fin n × Fin n)
    (u v : Fin n) (huv : u ≠ v) (q : ℕ) (F : Finset (Fin m))
    (hF : IsUnitFlow D F u v q) :
    (∃ F' : Finset (Fin m), IsUnitFlow D F' u v (q + 1)) ∨
      ∃ S : Finset (Fin n), IsCut S u v ∧ outCount D S = q := by sorry
end DirKECC1549.Main
