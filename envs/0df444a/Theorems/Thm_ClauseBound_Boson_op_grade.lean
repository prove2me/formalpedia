-- Prove2me | Theorems.Thm_ClauseBound_Boson_op_grade
-- name    : ClauseBound.Boson.op_grade
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:44:44.791378+00:00
-- url     : https://prove2.me/theorems/075ae69f-0ff3-488e-bc2d-c19a5a6e26b2
-- title:
--   Boson: op grade
-- statement:
--   a[r] raises the weight by r.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Basic.lean#L86-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Basic.lean#L86-L103

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Basic
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open Basic

theorem ClauseBound.Boson.op_grade {a : List ℕ} {r : ℤ} {π σ : Multiset ℕ} (h : op a r π σ ≠ 0) : (π.sum : ℤ) = σ.sum + r := by sorry
