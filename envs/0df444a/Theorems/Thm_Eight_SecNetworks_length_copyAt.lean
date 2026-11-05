-- Prove2me | Theorems.Thm_Eight_SecNetworks_length_copyAt
-- name    : Eight.SecNetworks.length_copyAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:59:59.012021+00:00
-- url     : https://prove2.me/theorems/92619a3d-8b18-4cd8-be91-899c0f41ab0c
-- title:
--   Sec Networks: length copy At
-- statement:
--   In a setting of (K − 1)λ bits every copy has λ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Clique.lean#L54-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Clique.lean#L54-L58

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_StepMachines_Prog_NetVal
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_Clique
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Groundwork Groundwork.Prog Finset

theorem Eight.SecNetworks.length_copyAt {K lam : ℕ} (w w' : Fin K) (h : w' ≠ w) {z : List Bool} (hz : z.length = (K - 1) * lam) :
    (copyAt lam w w' z).length = lam := by sorry
