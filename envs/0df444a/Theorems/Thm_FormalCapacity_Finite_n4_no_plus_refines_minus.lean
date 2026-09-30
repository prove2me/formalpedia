-- Prove2me | Theorems.Thm_FormalCapacity_Finite_n4_no_plus_refines_minus
-- name    : FormalCapacity.Finite.n4_no_plus_refines_minus
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-07T18:09:16.903052+00:00
-- url     : https://prove2.me/theorems/3fe88458-6f0b-48e4-bfa2-e49acadca35a
-- title:
--   No forward refinement coupling for the four-label square
-- statement:
--   Let $(P_0,P_1)=(12\mid34,1\mid2\mid3\mid4)$ and $(Q_0,Q_1)=(1\mid2\mid34,12\mid3\mid4)$. Write $P\preceq Q$ when every source block is contained in a target block. There is no nonnegative rational table $K$ with every row and column sum $1/2$ satisfying
--
--   $$K_{ij}=0\quad\text{whenever }P_i\not\preceq Q_j.$$
--
--   Equivalently, no coupling in the specified rational two-atom model transports the uniform positive law to the uniform negative law while being supported on refinement. Together with equality of their block coordinates, this distinguishes first-order statistical agreement from compatibility with directed coarsening. The coefficient field remains $\mathbb Q$, and the refinement direction is fine to coarse.
-- source:
--   The four-label correlation threshold, Proposition 1.1, forward refinement obstruction. Unpublished research note (2026), N4_BLOCK_CORRELATION_NOTE.md, SHA-256 a9b67c132ca0e0af807fb917ca2322833b84e162c45a4da7329ee88fbe4f1c83. Exact formal source: formal_capacity/FormalCapacity/Finite/N4.lean, lines 130–139, declaration FormalCapacity.Finite.n4_no_plus_refines_minus, source-file SHA-256 280e7a5db975df324036a6fa34b42c689519d3d508ba10e85a18645f77ddeb26. Local source archive; no public repository URL or commit is asserted. Upload checked with Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

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

theorem FormalCapacity.Finite.n4_no_plus_refines_minus :
    ¬ ∃ K : UniformTwoCoupling,
      ∀ i j, ¬ (plusAtom i).Refines (minusAtom j) → K.mass i j = 0 := by
  sorry
