-- Prove2me | Theorems.Thm_ClauseBound_Boson_Text_coef_mon
-- name    : ClauseBound.Boson.Text.coef_mon
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:19:43.877385+00:00
-- url     : https://prove2.me/theorems/4ec88868-1bb6-4748-b46b-3e9f50ac3d50
-- title:
--   Text: coef mon
-- statement:
--   The Text construction uses the coef mon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L144-L151
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L144-L151

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

theorem ClauseBound.Boson.Text.coef_mon (π σ : Multiset ℕ) : coef π (mon σ) = if π = σ then 1 else 0 := by sorry
