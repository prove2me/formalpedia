-- Prove2me | Theorems.Thm_CircuitLowerBound_Alg_uOf_eq
-- name    : CircuitLowerBound.Alg.uOf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:07:29.934201+00:00
-- url     : https://prove2.me/theorems/128ffcdc-fcb8-4bbe-b6aa-f6d4e03bb60d
-- title:
--   Alg: u Of eq
-- statement:
--   It is 1^m in unary, m the number of ones at the start of x.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Machine.lean#L66-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Machine.lean#L66-L69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Alg_Parse
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_PaddedDescent_Host
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Machine
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing Parse
open CircuitLowerBound.Alg

theorem CircuitLowerBound.Alg.uOf_eq (x : List Bool) : uOf x = List.replicate (ones x) () := by sorry
