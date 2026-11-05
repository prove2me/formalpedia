-- Prove2me | Theorems.Thm_Eight_ViaGrouping_stValue
-- name    : Eight.ViaGrouping.stValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:11:40.833121+00:00
-- url     : https://prove2.me/theorems/ee74df8f-562b-435f-9583-bd0c7ab47103
-- title:
--   Via Grouping: st Value
-- statement:
--   **«… so the value equals Z»** (end of the paragraph «The algorithm»): the (K, L)-clique with the
--   tables W̃ has the value of the network, if Y_{γ,γ'} ≤ L. Same as in the paper, except that the value
--   of the (K, L)-clique is written with one string per edge (`Paper.cliqueValue`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L464-L469
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L464-L469

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Table

theorem Eight.ViaGrouping.stValue : StValue := by sorry
