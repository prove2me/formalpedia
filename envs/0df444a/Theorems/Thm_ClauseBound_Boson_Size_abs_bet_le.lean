-- Prove2me | Theorems.Thm_ClauseBound_Boson_Size_abs_bet_le
-- name    : ClauseBound.Boson.Size.abs_bet_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:38:08.914679+00:00
-- url     : https://prove2.me/theorems/e6170b8d-ecf7-453a-a809-8c0382c2a646
-- title:
--   Size: abs bet le
-- statement:
--   |C(r − 1, n − 1)| ≤ 2^{2W} for n ≤ W and |r| ≤ W.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Size.lean#L32-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Size.lean#L32-L36

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

theorem ClauseBound.Boson.Size.abs_bet_le {W n : ℕ} (hW : 1 ≤ W) (hn : n ≤ W) {r : ℤ} (h1 : -(W : ℤ) ≤ r) (h2 : r ≤ W) : |bet n r| ≤ 2 ^ (2 * W) := by sorry
