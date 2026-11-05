-- Prove2me | Theorems.Thm_ClauseBound_Boson_Text_foldl_smul
-- name    : ClauseBound.Boson.Text.foldl_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:01:20.285922+00:00
-- url     : https://prove2.me/theorems/1fc49342-ded2-4f1c-8d95-b845540188c0
-- title:
--   Text: foldl smul
-- statement:
--   The Text construction uses the foldl smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L157-L160
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L157-L160

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

theorem ClauseBound.Boson.Text.foldl_smul (ks : List ℤ) : ∀ (c : ℤ) (f : Rg), ks.foldl (fun g k => nabPos k g) (c • f) = c • ks.foldl (fun g k => nabPos k g) f := by sorry
