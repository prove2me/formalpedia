-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_cap_symm
-- name    : Eight.ViaGrouping.Table.cap_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:08:58.816766+00:00
-- url     : https://prove2.me/theorems/8c285017-4528-4847-989e-a852a2778942
-- title:
--   Table: cap symm
-- statement:
--   The numbers c_{a,b} that are given are symmetric.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L72-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L72-L75

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Groundwork_Prog_NetE_cap_symm

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
omit [HasSize C]

theorem Eight.ViaGrouping.Table.cap_symm (h : IsNetworkP Np c N P B τ S) (a b : Fin g) : Np.cap c a b = Np.cap c b a := by sorry
