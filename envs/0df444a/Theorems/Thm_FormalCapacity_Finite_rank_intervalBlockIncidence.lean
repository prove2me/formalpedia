-- Prove2me | Theorems.Thm_FormalCapacity_Finite_rank_intervalBlockIncidence
-- name    : FormalCapacity.Finite.rank_intervalBlockIncidence
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-07T18:07:59.514982+00:00
-- url     : https://prove2.me/theorems/a20cfd26-dfae-4340-a3b5-d9cc1e3cfbe3
-- title:
--   Exact interval-block incidence rank
-- statement:
--   Let $n>0$ be an integer. Let $\mathcal I_n$ be all nonempty intervals in the ordered label set $1,\ldots,n$, and let $\Pi_n^{\rm int}$ consist of genuine finite partitions whose blocks are endpoint-certified intervals. For the rational linear map $(T_{\rm int}c)(P)=\sum_{I\in P}c_I$,
--
--   $$\dim_{\mathbb Q}\operatorname{range}T_{\rm int}=\binom n2+1.$$
--
--   This is the exact information rank of interval-block incidence on compositions, in its transposed representation. Both the full interval coefficient space and all certified interval partitions occur in the statement. The positive-size hypothesis is explicit; the result does not assert the displayed formula at $n=0$.
-- source:
--   The four-label correlation threshold, Theorem 2.2, rank assertion in (2.8). Unpublished research note (2026), N4_BLOCK_CORRELATION_NOTE.md, SHA-256 a9b67c132ca0e0af807fb917ca2322833b84e162c45a4da7329ee88fbe4f1c83. Exact formal source: formal_capacity/FormalCapacity/Finite/IntervalRank.lean, lines 324–332, declaration FormalCapacity.Finite.rank_intervalBlockIncidence, source-file SHA-256 5c52374871945aee752877ecf9e185074359f7d10cb473513e967665879afb4d. Local source archive; no public repository URL or commit is asserted. Upload checked with Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_capacityFinitePartitions
import Definitions.Def_capacityIntervalIncidence

set_option autoImplicit false

/-!
# Exact rank for interval partitions

Rows are nonempty intervals of Fin n, represented by their ordered
endpoints. Columns are genuine Finpartitions all of whose blocks carry an
endpoint certificate. This realizes compositions without choosing a cut-set
encoding.
-/

open FormalCapacity.Finite

open scoped BigOperators
open Finset Module Set

theorem FormalCapacity.Finite.rank_intervalBlockIncidence (n : ℕ) (hn : 0 < n) :
    finrank ℚ (intervalBlockIncidenceTranspose n).range = n.choose 2 + 1 := by
  sorry
