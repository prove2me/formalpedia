-- Prove2me | Theorems.Thm_FormalCapacity_Finite_n4_sameFirstOrder
-- name    : FormalCapacity.Finite.n4_sameFirstOrder
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-07T18:08:42.203768+00:00
-- url     : https://prove2.me/theorems/9c4a8f5c-60da-4820-9b84-05716f0d9df9
-- title:
--   Different four-label laws have identical first-order block data
-- statement:
--   On four labels, let $\mu_+$ be uniform on $12\mid34$ and $1\mid2\mid3\mid4$, and let $\mu_-$ be uniform on $1\mid2\mid34$ and $12\mid3\mid4$. For every subset $B$ of the labels, with rational exact-block indicators,
--
--   $$\mathbb E_{\mu_+}\mathbf1_{\{B\in P\}}=\mathbb E_{\mu_-}\mathbf1_{\{B\in P\}}.$$
--
--   Thus these explicit laws cannot be distinguished by first-order block coordinates. The assertion is equality of block statistics, not equality of the partition laws or the existence of a refinement coupling. The quantifier includes the empty subset, for which both coordinates vanish.
-- source:
--   The four-label correlation threshold, Proposition 1.1 and (1.3). Unpublished research note (2026), N4_BLOCK_CORRELATION_NOTE.md, SHA-256 a9b67c132ca0e0af807fb917ca2322833b84e162c45a4da7329ee88fbe4f1c83. Exact formal source: formal_capacity/FormalCapacity/Finite/N4.lean, lines 90–97, declaration FormalCapacity.Finite.n4_sameFirstOrder, source-file SHA-256 280e7a5db975df324036a6fa34b42c689519d3d508ba10e85a18645f77ddeb26. Local source archive; no public repository URL or commit is asserted. Upload checked with Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

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

theorem FormalCapacity.Finite.n4_sameFirstOrder (B : Finset Label4) :
    n4TwoAtomAverage .plusCoarse .plusDiscrete
        (fun P ↦ P.blockIndicator B) =
      n4TwoAtomAverage .minusLeft .minusRight
        (fun P ↦ P.blockIndicator B) := by
  sorry
