-- Prove2me | Theorems.Thm_Erdos146_binaryEntropy_continuous
-- name    : Erdos146.binaryEntropy_continuous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:39:41.365262+00:00
-- url     : https://prove2.me/theorems/66e7d018-f941-4f7d-a6c2-86ff0be65ee7
-- title:
--   Binary entropy is continuous
-- statement:
--   The binary entropy function is continuous — needed to compare the thresholds $A(\tau)$ and $C(\tau)$ over a range of Hamming radii rather than at a point.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L9421-L9422

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

@[fun_prop] theorem Erdos146.binaryEntropy_continuous : Continuous binaryEntropy := by sorry
