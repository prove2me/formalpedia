-- Prove2me | Theorems.Thm_ExplicitCost_c_eq
-- name    : ExplicitCost.c_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:24:36.944192+00:00
-- url     : https://prove2.me/theorems/77983f98-1b6c-4711-bc83-04026e6784e4
-- title:
--   Explicit Cost: c eq
-- statement:
--   c_{a,a'} is the number `capG` computed from the pieces, the grid and the index y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternValues.lean#L79-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternValues.lean#L79-L80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_Printed_Coding
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternValues
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {D : PiecesCounted.Data} {c g lam y : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.c_eq {a b : Fin (nParts g g tr)} (hab : a ≠ b) : (patternNet D c g tr lam y W).c a b = capG (piecesOf D c) g g tr 0 lam y a b := by sorry
