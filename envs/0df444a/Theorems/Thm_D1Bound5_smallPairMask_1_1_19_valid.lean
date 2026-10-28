-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_1_1_19_valid
-- name    : D1Bound5.smallPairMask_1_1_19_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:36:33.229144+00:00
-- url     : https://prove2.me/theorems/cb1c405b-466f-4313-a0e6-c5ad9bcdd2e2
-- title:
--   Validity of coordinate square mask smallPairMask_1_1_19
-- statement:
--   The mask `smallPairMask_1_1_19` accepts every square modulo 71 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 1 and ν = 1. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_1_1.lean, lines 103-105, SHA-256 1d8f95bc4892e90bd05d01e91bc00986257d3ff7687a0c2cb9996f150d2f1c65. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_1_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



























































theorem _root_.D1Bound5.smallPairMask_1_1_19_valid : CoordinateSquareMaskValid 1 1 70 smallPairMask_1_1_19 := by sorry




















end D1Bound5
end
