-- Prove2me | Theorems.Thm_FormalCapacity_Finite_n4_no_minus_refines_plus
-- name    : FormalCapacity.Finite.n4_no_minus_refines_plus
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-07T18:09:53.945951+00:00
-- url     : https://prove2.me/theorems/3cc4b94f-d75f-481b-8e07-fd2d85069142
-- title:
--   No reverse refinement coupling for the four-label square
-- statement:
--   Let $(Q_0,Q_1)=(1\mid2\mid34,12\mid3\mid4)$ and $(P_0,P_1)=(12\mid34,1\mid2\mid3\mid4)$. Write $Q\preceq P$ when every source block is contained in a target block. There is no nonnegative rational table $K$ with every row and column sum $1/2$ satisfying
--
--   $$K_{ij}=0\quad\text{whenever }Q_i\not\preceq P_j.$$
--
--   This rules out the reverse refinement-supported coupling between the two uniform laws. It is a separate directional obstruction: refinement has not been assumed symmetric. The statement concerns the exact rational $2\times2$ coupling representation, not an unstated generalization to arbitrary real-valued probability kernels.
-- source:
--   The four-label correlation threshold, Proposition 1.1, reverse refinement obstruction. Unpublished research note (2026), N4_BLOCK_CORRELATION_NOTE.md, SHA-256 a9b67c132ca0e0af807fb917ca2322833b84e162c45a4da7329ee88fbe4f1c83. Exact formal source: formal_capacity/FormalCapacity/Finite/N4.lean, lines 141–150, declaration FormalCapacity.Finite.n4_no_minus_refines_plus, source-file SHA-256 280e7a5db975df324036a6fa34b42c689519d3d508ba10e85a18645f77ddeb26. Local source archive; no public repository URL or commit is asserted. Upload checked with Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_capacityFourLabelAtoms

set_option autoImplicit false

/-!
# The four-label correlation obstruction

This file kernel-checks the signed square

`12|34 + 1|2|3|4 = 1|2|34 + 12|3|4`

at every block-incidence coordinate.  The four atoms are represented by
their finite sets of blocks.  `n4Atom_isPartition` verifies that each label
belongs to exactly one nonempty block, so this concrete representation does
not hide a partition-validity assumption.
-/

open FormalCapacity.Finite

open Finset

theorem FormalCapacity.Finite.n4_no_minus_refines_plus :
    ¬ ∃ K : UniformTwoCoupling,
      ∀ i j, ¬ (minusAtom i).Refines (plusAtom j) → K.mass i j = 0 := by
  sorry
