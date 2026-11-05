-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_lt_one
-- name    : ClauseBound.Inst.Half.lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:20.182616+00:00
-- url     : https://prove2.me/theorems/3979372f-0838-495b-96df-cc3be5a3855c
-- title:
--   Half: lt one
-- statement:
--   1/√2 < 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfEnd.lean#L27-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfEnd.lean#L27-L30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Inst_HalfEnd
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half

theorem ClauseBound.Inst.Half.lt_one : 1 / Real.sqrt 2 < 1 := by sorry
