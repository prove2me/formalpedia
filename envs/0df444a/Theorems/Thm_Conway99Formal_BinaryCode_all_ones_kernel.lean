-- Prove2me | Theorems.Thm_Conway99Formal_BinaryCode_all_ones_kernel
-- name    : Conway99Formal.BinaryCode.all_ones_kernel
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T19:03:45.839979+00:00
-- url     : https://prove2.me/theorems/9b8375bd-bdd3-433e-9694-0e9a7510bbf7
-- title:
--   The all-ones vector lies in the binary adjacency kernel
-- statement:
--   V is the finite vertex set, G is its graph, and adjacency G is its matrix over ZMod 2; x, y, and u are binary words indexed by V. `weight` is Hamming weight. Rooted matrices are the source-defined blocks at the chosen root. The exact type records which results assume SRG parameters (99,14,1,2) and which are general binary linear algebra.
--   Variable guide: V is the finite vertex set, G is its graph, and adjacency G is its matrix over ZMod 2; x, y, and u are binary words indexed by V. `weight` is Hamming weight. Rooted matrices are the source-defined blocks at the chosen root. The exact type records which results assume SRG parameters (99,14,1,2) and which are general binary linear algebra.
--   The source declaration has the exact hypotheses and variable types preserved in `variables_and_premises`. Under those assumptions, it concludes:
--   \[\texttt{(adjacency G).mulVec (fun \_ => (1 : ZMod 2)) = 0}\]
--   This is a binary-code or rooted-matrix consequence under exactly the assumptions in the source declaration. SRG parameters are retained where stated; the result is conditional and does not assert graph existence.
-- source:
--   Exact original Lean source: formalization/2026-10-03/binary-code/BinaryCode.lean#L141-L148; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 1437e9cd690e050f604a603b7826fef50f4ef1f6c0d21ef32c66c9793cb943e4. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/binary-code/BinaryCode.lean#L141-L148.

import Definitions.Def_QaAlgebra_BinaryCode
import Mathlib

namespace Conway99Formal.BinaryCode
end Conway99Formal.BinaryCode

set_option autoImplicit false

/-!
Binary adjacency-code identities for an actual SRG(99,14,1,2).
Sources: Conway99/Conway99/Claims/C01srgcorealgebra.lean §4;
Conway99/Conway99/Claims/C04finitefieldranks.lean §1;
Conway99/results/R003_enriched_binary_code_odd_cross_rank.md §1;
Conway99/results/R017_binary_genus2_smith_weight60.md §1.
-/

open Conway99Formal.BinaryCode

open Matrix SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem Conway99Formal.BinaryCode.all_ones_kernel (h : G.IsSRGWith 99 14 1 2) :
    (adjacency G).mulVec (fun _ => (1 : ZMod 2)) = 0 := by sorry
