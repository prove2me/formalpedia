-- Prove2me | Theorems.Thm_Eight_ViaGrouping_stLemGrouping_of
-- name    : Eight.ViaGrouping.stLemGrouping_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:01:04.271204+00:00
-- url     : https://prove2.me/theorems/30486659-3ee0-47d7-8bf9-a14771c23840
-- title:
--   Via Grouping: st Lem Grouping of
-- statement:
--   **Lemma 1 for the algorithm of its proof** (`StLemGrouping`), from the three steps «a good
--   grouping exists … fix the first good one», «one entry costs …» and «so the value equals Z».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L290-L293
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L290-L293

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_StepMachines_Math_RebalanceArith
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Main
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Cost

theorem Eight.ViaGrouping.stLemGrouping_of (hS : StSearch) (hT : StTable) (hV : StValue) : StLemGrouping := by sorry
