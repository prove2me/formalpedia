-- Prove2me | Theorems.Thm_CountKSat_HostW_emit_runs
-- name    : CountKSat.HostW.emit_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:19:56.962194+00:00
-- url     : https://prove2.me/theorems/561e9584-4872-4f5a-bf09-ca71c9dfab0d
-- title:
--   Host W: emit runs
-- statement:
--   The Host W construction uses the emit runs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L112-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L112-L125

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Machine_Host
import Definitions.Def_CountKSat_Host
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
open CountKSat CountKSat.HostW
open Groundwork Groundwork.TM Groundwork.Host Turing

theorem CountKSat.HostW.emit_runs (M B N : List Sym) : ∀ (l W : List Bool),
    emit.Runs none (withIO W (st (List.replicate l.length .R ++ M) (l.map Sym.bit) B N)) (2 * l.length + 1)
      (withIO (l.reverse ++ W) (st M [] B N))
  := by sorry
