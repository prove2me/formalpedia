-- Prove2me | Theorems.Thm_Conway99Formal_SrgCore_overFin_srg
-- name    : Conway99Formal.SrgCore.overFin_srg
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T03:21:50.055359+00:00
-- url     : https://prove2.me/theorems/ab6e74e3-2042-4c15-acaf-a0c6b6400f05
-- title:
--   SRG parameters under canonical finite relabeling
-- statement:
--   If G has SRG parameters (99,14,1,2), its canonical relabeling on Fin(cardinality of G) has the same parameters.
--
--   $$G\text{ is SRG}(99,14,1,2)\Longrightarrow G_{\mathrm{Fin}(|V|)}\text{ is SRG}(99,14,1,2)$$
--
--   Role: This transfers the graph structure along the canonical finite-vertex equivalence.
-- source:
--   Exact original Lean source: formalization/2026-10-03/srg-core/Core.lean#L62-L101; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 64ce9b86d07bbd11a61266b80c3043c34c08d7f939471fff2c44dc34ff37904. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/srg-core/Core.lean#L62-L101.

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

theorem Conway99Formal.SrgCore.overFin_srg (h : G.IsSRGWith 99 14 1 2)
    [DecidableRel (G.overFin h.card).Adj] :
    (G.overFin h.card).IsSRGWith 99 14 1 2 := by sorry
