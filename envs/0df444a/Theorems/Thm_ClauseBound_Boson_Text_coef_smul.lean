-- Prove2me | Theorems.Thm_ClauseBound_Boson_Text_coef_smul
-- name    : ClauseBound.Boson.Text.coef_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:19:23.51825+00:00
-- url     : https://prove2.me/theorems/c7fb02c2-c125-4285-be59-587f93e34cc1
-- title:
--   Text: coef smul
-- statement:
--   The Text construction uses the coef smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L184-L186
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L184-L186

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

theorem ClauseBound.Boson.Text.coef_smul (π : Multiset ℕ) (c : ℤ) (f : Rg) : coef π (c • f) = c * coef π f := by sorry
