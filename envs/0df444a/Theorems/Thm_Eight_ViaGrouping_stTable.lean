-- Prove2me | Theorems.Thm_Eight_ViaGrouping_stTable
-- name    : Eight.ViaGrouping.stTable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:34:59.205687+00:00
-- url     : https://prove2.me/theorems/af6b75aa-ea49-4e61-9bb6-dba6589d0c7a
-- title:
--   Via Grouping: st Table
-- statement:
--   **«Cost», first two sentences.** «The sum defining W̃_γ(Θ) has at most (2^P)^{2g/K} = 2^{2gP/K}
--   terms, each a product of at most g² values. So |W̃_γ| < 2^{B'} with B' = ⌈2gP/K⌉ + g²B, and one
--   entry costs 2^{2gP/K}·poly(P + B)·τ operations.»
--   Different from the paper: ⌊2g/K⌋ nodes in a group, so P·⌊2g/K⌋ in place of 2gP/K; «at most 2^{B'}»
--   in place of «below 2^{B'}».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L447-L459
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L447-L459

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

theorem Eight.ViaGrouping.stTable : StTable := by sorry
