-- Prove2me | Theorems.Thm_CountKSat_HostW_pop3_runs
-- name    : CountKSat.HostW.pop3_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:18:40.632806+00:00
-- url     : https://prove2.me/theorems/62eba007-4432-4d44-9fa7-46307074e9e5
-- title:
--   Host W: pop3 runs
-- statement:
--   The Host W construction uses the pop3 runs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L131-L133
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L131-L133

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Machine_Host
import Definitions.Def_CountKSat_Host
set_option autoImplicit false
section
open CountKSat CountKSat.HostW
open Groundwork Groundwork.TM Groundwork.Host Turing

theorem CountKSat.HostW.pop3_runs (W : List Bool) (M A B N : List Sym) :
    pop3.Runs none (withIO W (st (.L :: .R :: .R :: M) A B N)) 1 (withIO W (st M A B N)) := by sorry
