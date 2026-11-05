-- Prove2me | Theorems.Thm_CountKSat_HostW_unpackQ_cons
-- name    : CountKSat.HostW.unpackQ_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:18:10.89451+00:00
-- url     : https://prove2.me/theorems/f78364d8-18b6-482c-99b4-8615796d694c
-- title:
--   Host W: unpack Q cons
-- statement:
--   The Host W construction uses the unpack Q cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L86-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L86-L88

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

theorem CountKSat.HostW.unpackQ_cons (b : Bool) (l : List Bool) : TM2.stepAux unpackQ none (withIO W (st (wd (b :: l) ++ M) A B N)) =
    ⟨some (), none, withIO W (st (wd l ++ (.R :: M)) (.bit b :: A) B N)⟩ := by sorry
