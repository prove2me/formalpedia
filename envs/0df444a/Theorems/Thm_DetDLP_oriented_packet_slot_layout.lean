-- Prove2me | Theorems.Thm_DetDLP_oriented_packet_slot_layout
-- name    : DetDLP.oriented_packet_slot_layout
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T13:57:25.305805+00:00
-- url     : https://prove2.me/theorems/7d8af6e7-db4d-476b-853e-80f866ef7751
-- title:
--   An oriented, collision-free slot layout for every edge of the network
-- statement:
--   Let a bipartite multigraph have $M$ edges and maximum degree $\Delta$. Under $2\Delta r^{4a}\le M$ and $2^a r^{2a}\le M$, the vertices admit $a$-coordinate labels over $r$ symbols and every edge has a distinct packet and slot address. There are at most $3M$ slots in packets of length $2^a$. In each coordinate the packet tag fixes the unordered endpoint symbols, and the corresponding binary slot bit determines their orientation. Each symbol occurs at most $2M/r$ times on either side in any coordinate.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Packet packing lemma, Section 5.1 and its scalar contraction counterpart.

import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

open Finset

namespace DetDLP

theorem oriented_packet_slot_layout (G : BipartiteMultigraph) (r a : ℕ) [NeZero r]
    (hsize : 2*G.maxDeg*(r^a)^4 ≤ G.nE) (hpad : 2^a*(r^a)^2 ≤ G.nE) :
    let Lab := Fin (r^a)
    let Tag := Fin a → Fin r × Fin r
    let ends (e : Fin G.nE) := if G.side (G.endpoints e).1 then (G.endpoints e).swap else G.endpoints e
    ∃ lab : Fin G.nV → Lab, ∃ B : ℕ,
      ∃ pos : Fin G.nE → (Fin B × Tag) × Fin (2^a),
        Function.Injective pos ∧ Fintype.card (Fin B × Tag)*2^a ≤ 3*G.nE ∧
        (∀ e i,
          let t := (pos e).1.2 i
          let row := finFunctionFinEquiv.symm (lab (ends e).1) i
          let col := finFunctionFinEquiv.symm (lab (ends e).2) i
          (row,col) = if (pos e).2.val.testBit i.val then (max t.1 t.2,min t.1 t.2)
            else (min t.1 t.2,max t.1 t.2)) ∧
        ∀ (right : Bool) (i : Fin a) (g : Fin r),
          r*Fintype.card {e : Fin G.nE //
            finFunctionFinEquiv.symm (lab (if right then (ends e).2 else (ends e).1)) i=g} ≤ 2*G.nE := by sorry

end DetDLP
