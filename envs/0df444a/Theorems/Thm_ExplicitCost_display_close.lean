-- Prove2me | Theorems.Thm_ExplicitCost_display_close
-- name    : ExplicitCost.display_close
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:24:12.551255+00:00
-- url     : https://prove2.me/theorems/06c4ab42-bee7-4052-bfc0-a766dce05ba1
-- title:
--   Explicit Cost: display close
-- statement:
--   The display reads only the numbers P_a, c_{a,b} of the procedures.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Cost.lean#L51-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Cost.lean#L51-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_SameRuns
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Cost
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.display_close {K g : ℕ} (O : NetQuery → Option ℤ) (c : NetInput) (N : Net g) (hK0 : 0 < K) (x : ℕ) : display (asked.close O) c N hK0 x = display asked.under c N hK0 x := by sorry
