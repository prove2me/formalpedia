-- Prove2me | Theorems.Thm_Conway99Formal_SrgCore_neighborhood_matching
-- name    : Conway99Formal.SrgCore.neighborhood_matching
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T04:00:06.677239+00:00
-- url     : https://prove2.me/theorems/e67913bc-0f1f-4bbd-852f-c8ee7854345f
-- title:
--   Each neighborhood induces a seven-edge matching
-- statement:
--   For a vertex u in an SRG(99,14,1,2), the induced graph on its neighbors has degree one at each vertex and exactly seven edges.
--
--   $$\deg_{G[N(u)]}(v)=1\ \forall v\in N(u),\qquad |E(G[N(u)])|=7$$
--
--   Role: It is a matching covering all fourteen neighbors of u.
-- source:
--   Exact original Lean source: formalization/2026-10-03/srg-core/Core.lean#L211-L229; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 64ce9b86d07bbdd11a61266b80c3043c34c08d7f939471fff2c44dc34ff37904. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/srg-core/Core.lean#L211-L229.

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

theorem Conway99Formal.SrgCore.neighborhood_matching (h : G.IsSRGWith 99 14 1 2) (u : V) :
    (∀ v : G.neighborSet u, (G.induce (G.neighborSet u)).degree v = 1) ∧
      (G.induce (G.neighborSet u)).edgeFinset.card = 7 := by sorry
