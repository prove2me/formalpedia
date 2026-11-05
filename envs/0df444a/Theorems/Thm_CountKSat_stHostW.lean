-- Prove2me | Theorems.Thm_CountKSat_stHostW
-- name    : CountKSat.stHostW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:52:43.156823+00:00
-- url     : https://prove2.me/theorems/519c1705-db64-41bc-bd0a-b53ad243d9b2
-- title:
--   Count KSat: st Host W
-- statement:
--   The host with a word as output: the interface statement `StHostW`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L282-L282
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L282-L282

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Machine_Host
import Definitions.Def_CountKSat_Host
set_option autoImplicit false
section
open CountKSat
open Groundwork Groundwork.TM Groundwork.Host Turing HostW

theorem CountKSat.stHostW : StHostW := by sorry
