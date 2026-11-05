-- Prove2me | Theorems.Thm_CountKSat_HostW_chkW_none
-- name    : CountKSat.HostW.chkW_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:18:49.545957+00:00
-- url     : https://prove2.me/theorems/638e03f0-7fd2-4185-a9fd-f9ba6157fbc6
-- title:
--   Host W: chk W none
-- statement:
--   The Host W construction uses the chk W none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L74-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L74-L76

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
variable (W : List Bool) (M A B N : List Sym)

theorem CountKSat.HostW.chkW_none : TM2.stepAux chkW none (withIO W (st (wd (none : Option (List Bool)) ++ M) A B N)) =
    ⟨some (), none, withIO W (st M A B N)⟩ := by sorry
