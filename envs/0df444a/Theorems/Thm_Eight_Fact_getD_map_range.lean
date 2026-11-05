-- Prove2me | Theorems.Thm_Eight_Fact_getD_map_range
-- name    : Eight.Fact.getD_map_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:52:52.768493+00:00
-- url     : https://prove2.me/theorems/54146588-654f-43f5-aa44-611ada3bb955
-- title:
--   Fact: get D map range
-- statement:
--   The bit number s < t of the word f 0, …, f (t − 1) is f s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L72-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L72-L73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Definitions.Def_Eight_SecCrossing_Chunk
import Definitions.Def_Eight_SecCrossing_MulOut
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Fact
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
open Eight.Fact

theorem Eight.Fact.getD_map_range {t s : ℕ} (h : s < t) (f : ℕ → Bool) : ((List.range t).map f).getD s false = f s := by sorry
