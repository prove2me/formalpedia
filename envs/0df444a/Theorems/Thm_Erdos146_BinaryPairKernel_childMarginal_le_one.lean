-- Prove2me | Theorems.Thm_Erdos146_BinaryPairKernel_childMarginal_le_one
-- name    : Erdos146.BinaryPairKernel.childMarginal_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:40:44.197945+00:00
-- url     : https://prove2.me/theorems/77ef37b8-c3b6-4c24-97ff-a5185fc555df
-- title:
--   The child marginal is at most one
-- statement:
--   Supporting fact for the two-bit pair kernel of Section 5, which governs how much conditional entropy a child bit can carry given its two parent bits. The child marginal is a probability: it never exceeds $1$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L10007-L10026

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

open Erdos146
open Erdos146.BinaryPairKernel
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.BinaryPairKernel.childMarginal_le_one (kernel : BinaryPairKernel) :
    kernel.childMarginal ≤ 1 := by sorry
