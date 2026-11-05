-- Prove2me | Theorems.Thm_ClauseBound_Boson_Text_nord_cons_pos
-- name    : ClauseBound.Boson.Text.nord_cons_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:20:20.626747+00:00
-- url     : https://prove2.me/theorems/229b2dac-1afa-4fc2-a966-8d697a8da72a
-- title:
--   Text: nord cons pos
-- statement:
--   A positive index: one more differentiation, applied first.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L174-L176
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L174-L176

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Text
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset MvPolynomial
open ClauseBound.Boson.Text

theorem ClauseBound.Boson.Text.nord_cons_pos {k : ℤ} (hk : 0 < k) (ks : List ℤ) (f : Rg) : nord (k :: ks) f = nord ks (nabPos k f) := by sorry
