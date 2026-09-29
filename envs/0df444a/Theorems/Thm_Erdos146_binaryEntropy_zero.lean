-- Prove2me | Theorems.Thm_Erdos146_binaryEntropy_zero
-- name    : Erdos146.binaryEntropy_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:39:28.699342+00:00
-- url     : https://prove2.me/theorems/0cd1c7ee-8fa2-46ca-8123-20f5173331e4
-- title:
--   Binary entropy vanishes at zero
-- statement:
--   The binary entropy function satisfies $h(0) = 0$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L9414-L9415

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

@[simp] theorem Erdos146.binaryEntropy_zero : binaryEntropy 0 = 0 := by sorry
