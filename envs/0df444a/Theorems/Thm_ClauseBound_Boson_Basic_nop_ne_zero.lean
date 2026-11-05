-- Prove2me | Theorems.Thm_ClauseBound_Boson_Basic_nop_ne_zero
-- name    : ClauseBound.Boson.Basic.nop_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:36:53.977613+00:00
-- url     : https://prove2.me/theorems/9d2a207b-db37-412d-b9ae-cd14efaaea5e
-- title:
--   Basic: nop ne zero
-- statement:
--   A nonzero entry of a normally ordered product comes from a nonzero entry of the family, after a
--   part of π or a part of σ has been removed.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Basic.lean#L29-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Basic.lean#L29-L46

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
open ClauseBound.Boson.Basic

theorem ClauseBound.Boson.Basic.nop_ne_zero {n : ℕ} {F : ℤ → Ker} {r : ℤ} {π σ : Multiset ℕ} (h : nop n F r π σ ≠ 0) :
    (∃ l ∈ π, F (r - l) (π.erase l) σ ≠ 0) ∨ ∃ k ∈ σ, F (r + k) π (σ.erase k) ≠ 0 := by sorry
