-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_half_le
-- name    : ClauseBound.Inst.Half.half_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:23:35.916721+00:00
-- url     : https://prove2.me/theorems/cbc44255-4dd9-46e9-8582-7d7e1cacf690
-- title:
--   Half: half le
-- statement:
--   1/2 ≤ 1/√2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfEnd.lean#L22-L24
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfEnd.lean#L22-L24

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Inst_HalfEnd
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half

theorem ClauseBound.Inst.Half.half_le : (1 / 2 : ℝ) ≤ 1 / Real.sqrt 2 := by sorry
