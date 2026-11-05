-- Prove2me | Theorems.Thm_ClauseBound_Boson_Size_abs_nop_le
-- name    : ClauseBound.Boson.Size.abs_nop_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:38:16.531815+00:00
-- url     : https://prove2.me/theorems/0fee9aa6-b251-40e9-a3ca-372effc79b09
-- title:
--   Size: abs nop le
-- statement:
--   One step of the recursion multiplies a bound B for the entries by at most 2^{4W+1}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Size.lean#L62-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Size.lean#L62-L89

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
open ClauseBound.Boson.Size

theorem ClauseBound.Boson.Size.abs_nop_le {W n : ℕ} (hW : 1 ≤ W) (hn : n ≤ W) {F : ℤ → Ker} {B : ℤ} (hB : 0 ≤ B)
    (hF : ∀ (r : ℤ) (π σ : Multiset ℕ), π.sum ≤ W → σ.sum ≤ W → |F r π σ| ≤ B) (r : ℤ) {π σ : Multiset ℕ} (hπ : π.sum ≤ W) (hσ : σ.sum ≤ W) :
    |nop n F r π σ| ≤ 2 ^ (4 * W + 1) * B := by sorry
