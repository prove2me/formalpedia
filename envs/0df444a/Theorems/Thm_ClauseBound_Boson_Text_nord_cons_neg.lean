-- Prove2me | Theorems.Thm_ClauseBound_Boson_Text_nord_cons_neg
-- name    : ClauseBound.Boson.Text.nord_cons_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:19:49.926032+00:00
-- url     : https://prove2.me/theorems/26729433-943b-4d77-948e-d17ef5ceeb2a
-- title:
--   Text: nord cons neg
-- statement:
--   A negative index: one more multiplication, on the left.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L169-L171
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L169-L171

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

theorem ClauseBound.Boson.Text.nord_cons_neg {k : ℤ} (hk : k < 0) (ks : List ℤ) (f : Rg) : nord (k :: ks) f = X (-k).toNat * nord ks f := by sorry
