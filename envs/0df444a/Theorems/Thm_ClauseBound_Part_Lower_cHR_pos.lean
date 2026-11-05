-- Prove2me | Theorems.Thm_ClauseBound_Part_Lower_cHR_pos
-- name    : ClauseBound.Part.Lower.cHR_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:05:41.704546+00:00
-- url     : https://prove2.me/theorems/14f9f01a-a043-440c-bd33-cb569324bf83
-- title:
--   Lower: c HR pos
-- statement:
--   The Lower construction uses the c HR pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L339-L341
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L339-L341

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Lower

theorem ClauseBound.Part.Lower.cHR_pos : 0 < cHR := by sorry
