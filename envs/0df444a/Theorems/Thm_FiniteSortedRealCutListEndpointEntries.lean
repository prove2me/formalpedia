-- Prove2me | Theorems.Thm_FiniteSortedRealCutListEndpointEntries
-- name    : FiniteSortedRealCutListEndpointEntries
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:26:06.895978+00:00
-- url     : https://prove2.me/theorems/72026d31-72b7-4c55-911a-be3079a7fb8f
-- title:
--   Finite Sorted Real Cut List Endpoint Entries
-- statement:
--   [Endpoint entries of a sorted cut list]
--   Let $L$ be a strictly increasing finite list of real numbers.  Suppose
--   $0\in L$, $1\in L$, and every entry of $L$ lies in the interval
--   $[0,1]$.  Then $L$ has length at least $2$.  Moreover its first entry is
--   $0$, and its last entry is $1$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `FiniteSortedRealCutListEndpointEntries`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FiniteSortedRealCutListEndpointEntries.lean#L1-L53

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
noncomputable section

lemma FiniteSortedRealCutListEndpointEntries
    (L : List ℝ)
    (hSorted : L.SortedLT)
    (hzero : (0 : ℝ) ∈ L) (hone : (1 : ℝ) ∈ L)
    (hbounds : ∀ t : ℝ, t ∈ L → 0 ≤ t ∧ t ≤ 1) :
    2 ≤ L.length ∧
      (∀ h : 0 < L.length, L[0]'h = 0) ∧
        (∀ h : L.length - 1 < L.length, L[L.length - 1]'h = 1) := by sorry
