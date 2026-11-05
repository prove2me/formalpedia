-- Prove2me | Theorems.Thm_CountKSat_HostW_size_le_of_reaches
-- name    : CountKSat.HostW.size_le_of_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:01:33.578543+00:00
-- url     : https://prove2.me/theorems/b693a6c1-e5fb-42b0-aef2-6546ff5e3a29
-- title:
--   Host W: size le of reaches
-- statement:
--   The Host W construction uses the size le of reaches property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L153-L156
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L153-L156

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Machine_Host
import Definitions.Def_CountKSat_Host
import Theorems.Thm_Groundwork_Host_size_le_of_reaches

set_option autoImplicit false
section
open CountKSat CountKSat.HostW
open Groundwork Groundwork.TM Groundwork.Host Turing
variable {M : Stepped (List Bool) (List Bool)}

theorem CountKSat.HostW.size_le_of_reaches {S t : ℕ} {w : List Bool} {s : M.σ} (h : M.Reaches S w s t) : size s ≤ S := by sorry
