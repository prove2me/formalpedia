-- Prove2me | Theorems.Thm_Eight_ViaGrouping_presentsP
-- name    : Eight.ViaGrouping.presentsP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:22:23.358196+00:00
-- url     : https://prove2.me/theorems/50073bd4-7fb7-4f0b-87c5-f1c4381bed42
-- title:
--   Via Grouping: presents P
-- statement:
--   The procedures `Np.toPaperNetwork` present the network `N.toPaperNetwork`; that the algorithm of
--   Definition 2 (iii) receives B is not needed for this. From `SecNetworks.presents_toPaperNetwork`,
--   applied to Np with the number B put in.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Search.lean#L45-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Search.lean#L45-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Search
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] {Np : Procs C} {c : C} {g K : ℕ} {N : Net g} {P B τ S : ℕ}

theorem Eight.ViaGrouping.presentsP (h : IsNetworkP Np c N P B τ S) : Np.toPaperNetwork.Presents c N.toPaperNetwork (2 * τ + 1) (S + (size c + 2 * size g + 4 * P + 6)) := by sorry
