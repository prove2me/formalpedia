-- Prove2me | Theorems.Thm_DeletionCode_FiniteConflictGraph_nonexceptional_trace
-- name    : DeletionCode.FiniteConflictGraph.nonexceptional_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:34:34.418597+00:00
-- url     : https://prove2.me/theorems/774cdeaa-1d0e-42be-ab38-2705c7925469
-- title:
--   Finite Conflict Graph: nonexceptional trace
-- statement:
--   Excluding the exceptional set rules out both short balanced traces and
--   nonseparated full-size traces. This applies to every such trace, not merely
--   to one specially chosen alignment.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteConflictGraph.lean#L82-L100
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteConflictGraph.lean#L82-L100

import Definitions.Def_DeletionCode_AlignmentTrace
import Definitions.Def_DeletionCode_BoundedWitnessWalk
import Mathlib.Combinatorics.SimpleGraph.Basic
import Definitions.Def_DeletionCode_FiniteConflictGraph
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteConflictGraph
open HeaderRecovery AlignmentTrace EditAlignment
variable {n : ℕ} {H : Type*}

theorem DeletionCode.FiniteConflictGraph.nonexceptional_trace {t k : ℕ} {label : Bits n → H}
    (x : Vertex t k label) (y : Bits n)
    (hxy : x.val ≠ y) (hlabel : label x.val = label y)
    (d : ℕ) (trace : Trace) (hd : d ≤ t)
    (hsource : trace.source = List.ofFn x.val)
    (htarget : trace.target = List.ofFn y)
    (hdel : trace.deletions = d) (hins : trace.insertions = d) :
    trace.deletions = t ∧ trace.insertions = t ∧
      Separated (4 * windowLength k) trace := by sorry
