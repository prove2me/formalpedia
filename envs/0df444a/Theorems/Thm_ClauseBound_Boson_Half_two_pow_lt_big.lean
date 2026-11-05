-- Prove2me | Theorems.Thm_ClauseBound_Boson_Half_two_pow_lt_big
-- name    : ClauseBound.Boson.Half.two_pow_lt_big
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:39:28.952215+00:00
-- url     : https://prove2.me/theorems/1a88a31a-4e5a-4a0a-86f6-20b9ac7ec58a
-- title:
--   Half: two pow lt big
-- statement:
--   The Half construction uses the two pow lt big property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Half.lean#L123-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Half.lean#L123-L124

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_ClauseBound_Boson_HalfSum
import Definitions.Def_ClauseBound_Rec_Number
import Definitions.Def_ClauseBound_Boson_Half
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Half

theorem ClauseBound.Boson.Half.two_pow_lt_big {h e : ℕ} (he : e ≤ eL h + eR h) : (2 : ℤ) ^ e < 2 ^ big h := by sorry
