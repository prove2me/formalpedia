-- Prove2me | Theorems.Thm_ExplicitCost_size_listUnit
-- name    : ExplicitCost.size_listUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:07:39.077081+00:00
-- url     : https://prove2.me/theorems/6406ecea-28a3-4144-9c1a-061b3655a48b
-- title:
--   Explicit Cost: size list Unit
-- statement:
--   A list of n units has size 2n + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Base.lean#L29-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Base.lean#L29-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_CountedRecursion_Brute
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Base
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines Printed

theorem ExplicitCost.size_listUnit (l : List Unit) : size l = 2 * l.length + 1 := by sorry
