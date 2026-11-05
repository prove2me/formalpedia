-- Prove2me | Theorems.Thm_CircuitLowerBound_stRestart
-- name    : CircuitLowerBound.stRestart
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:47:11.256699+00:00
-- url     : https://prove2.me/theorems/d3ca7ccf-622d-48ca-bbaa-2badd0ec6f5b
-- title:
--   Circuit Lower Bound: st Restart
-- statement:
--   A machine that is started again after every answer can be replaced by an oracle machine.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Restart.lean#L94-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Restart.lean#L94-L104

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Oracle_Runs
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Restart
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Turing Groundwork.TM
open Oracle

theorem CircuitLowerBound.stRestart : StRestart := by sorry
