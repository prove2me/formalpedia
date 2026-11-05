-- Prove2me | Theorems.Thm_CountKSat_HostW_unpack_runs
-- name    : CountKSat.HostW.unpack_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:18:53.016549+00:00
-- url     : https://prove2.me/theorems/bb7e6bae-7788-4f88-b5c9-83140711fbef
-- title:
--   Host W: unpack runs
-- statement:
--   The Host W construction uses the unpack runs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L99-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L99-L110

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

theorem CountKSat.HostW.unpack_runs (W : List Bool) (B N : List Sym) : ∀ (w : List Bool) (M A : List Sym),
    unpack.Runs none (withIO W (st (wd w ++ M) A B N)) (2 * w.length + 1)
      (withIO W (st (List.replicate w.length .R ++ M) ((w.map Sym.bit).reverse ++ A) B N))
  := by sorry
