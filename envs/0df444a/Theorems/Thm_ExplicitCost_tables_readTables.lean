-- Prove2me | Theorems.Thm_ExplicitCost_tables_readTables
-- name    : ExplicitCost.tables_readTables
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:07:23.082419+00:00
-- url     : https://prove2.me/theorems/d62a8c5c-cc21-4e19-abcb-2424cd48bd43
-- title:
--   Explicit Cost: tables read Tables
-- statement:
--   The tables read back from the answers of `W`, `readTables (answersOf K lam W)`, give the same
--   oracle `tables K lam` as `W` itself.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Base.lean#L38-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Base.lean#L38-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_CountedRecursion_Brute
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Base
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines Printed

theorem ExplicitCost.tables_readTables (K lam : ℕ) (W : ℕ → List Bool → ℤ) : tables K lam (readTables (answersOf K lam W)) = tables K lam W := by sorry
