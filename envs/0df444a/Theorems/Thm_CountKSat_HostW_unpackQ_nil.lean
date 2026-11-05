-- Prove2me | Theorems.Thm_CountKSat_HostW_unpackQ_nil
-- name    : CountKSat.HostW.unpackQ_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:18:52.086887+00:00
-- url     : https://prove2.me/theorems/42e2a52c-6e1b-4001-839f-9d3ef7327822
-- title:
--   Host W: unpack Q nil
-- statement:
--   The Host W construction uses the unpack Q nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L82-L84
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L82-L84

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

theorem CountKSat.HostW.unpackQ_nil : TM2.stepAux unpackQ none (withIO W (st (wd ([] : List Bool) ++ M) A B N)) =
    ⟨none, none, withIO W (st M A B N)⟩ := by sorry
