-- Prove2me | Theorems.Thm_ClauseBound_Boson_abs_op_le
-- name    : ClauseBound.Boson.abs_op_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:18:27.828978+00:00
-- url     : https://prove2.me/theorems/47fbcfa2-b2aa-4206-8b21-2924a75195c9
-- title:
--   Boson: abs op le
-- statement:
--   If all weights and parts are at most W, an entry of the matrix of a[r] is at most
--   2^{(4W+1)·(number of parts of a)} in absolute value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Size.lean#L95-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Size.lean#L95-L107

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Rec_Window
import Definitions.Def_ClauseBound_Boson_Size
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset

theorem ClauseBound.Boson.abs_op_le {W : ℕ} (hW : 1 ≤ W) (a : List ℕ) (ha : ∀ n ∈ a, n ≤ W) (r : ℤ) {π σ : Multiset ℕ} (hπ : π.sum ≤ W) (hσ : σ.sum ≤ W) :
    |op a r π σ| ≤ 2 ^ ((4 * W + 1) * a.length) := by sorry
