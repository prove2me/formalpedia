-- Prove2me | Theorems.Thm_ClauseBound_Boson_Size_card_toFinset_le
-- name    : ClauseBound.Boson.Size.card_toFinset_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:38:05.581135+00:00
-- url     : https://prove2.me/theorems/7592419a-7c32-4e9c-bde1-aaacfd07da6c
-- title:
--   Size: card to Finset le
-- statement:
--   A monomial of weight at most W has at most W + 1 different parts.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Size.lean#L51-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Size.lean#L51-L53

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

theorem ClauseBound.Boson.Size.card_toFinset_le {π : Multiset ℕ} {W : ℕ} (h : π.sum ≤ W) : #π.toFinset ≤ W + 1 := by sorry
