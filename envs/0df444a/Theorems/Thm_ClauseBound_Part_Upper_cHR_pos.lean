-- Prove2me | Theorems.Thm_ClauseBound_Part_Upper_cHR_pos
-- name    : ClauseBound.Part.Upper.cHR_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:01:55.115327+00:00
-- url     : https://prove2.me/theorems/ff748bf8-7cec-4777-812d-571130a149f0
-- title:
--   Upper: c HR pos
-- statement:
--   c = π·√(2/3) is positive.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Upper.lean#L26-L28
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Upper.lean#L26-L28

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Upper
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Upper

theorem ClauseBound.Part.Upper.cHR_pos : 0 < cHR := by sorry
