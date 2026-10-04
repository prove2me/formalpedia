-- Prove2me | Theorems.Thm_Conway99Formal_SrgCore_edge_in_12_induced_C4_distinct
-- name    : Conway99Formal.SrgCore.edge_in_12_induced_C4_distinct
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T04:01:35.489113+00:00
-- url     : https://prove2.me/theorems/0f1ac592-736c-4dce-8913-9c2cb6f0f9f5
-- title:
--   Twelve induced four-cycles contain each edge
-- statement:
--   For every edge xy in an SRG(99,14,1,2), exactly twelve ordered pairs (a,b) make y-a-b-x-y an induced four-cycle, with the nonedges and endpoint inequalities shown.
--
--   $$|\{(a,b): ya,ab,bx\in E(G),\ xa,yb\notin E(G),\ a\ne x,\ b\ne y\}|=12$$
--
--   Role: The ordered pair records the two intermediate vertices and counts each cycle in the source orientation.
-- source:
--   Exact original Lean source: formalization/2026-10-03/srg-core/Core.lean#L231-L334; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 64ce9b86d07bbdd11a61266b80c3043c34c08d7f939471fff2c44dc34ff37904. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/srg-core/Core.lean#L231-L334.

import Mathlib

namespace Conway99Formal.SrgCore
end Conway99Formal.SrgCore

set_option autoImplicit false

/-! Graph-owned parameter and adjacency identities for a hypothetical SRG(99,14,1,2).
Sources: `Conway99/Conway99/Core.lean` §§1–3, 8.1;
`Conway99/Conway99/Claims/C01srgcorealgebra.lean` §§0, 3, 6;
`Conway99/results/R005_star_complement_square_discriminant.md`.
-/

open Conway99Formal.SrgCore

open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem Conway99Formal.SrgCore.edge_in_12_induced_C4_distinct (h : G.IsSRGWith 99 14 1 2)
    (x y : V) (hxy : G.Adj x y) :
    ((univ : Finset (V × V)).filter fun p =>
      G.Adj y p.1 ∧ G.Adj p.1 p.2 ∧ G.Adj p.2 x ∧
        ¬ G.Adj x p.1 ∧ ¬ G.Adj y p.2 ∧ p.1 ≠ x ∧ p.2 ≠ y).card = 12 := by sorry
