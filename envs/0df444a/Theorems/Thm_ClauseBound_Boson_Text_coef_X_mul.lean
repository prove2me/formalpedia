-- Prove2me | Theorems.Thm_ClauseBound_Boson_Text_coef_X_mul
-- name    : ClauseBound.Boson.Text.coef_X_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:19:39.295203+00:00
-- url     : https://prove2.me/theorems/208409c9-d928-41f0-9c90-6c5babfcd8e5
-- title:
--   Text: coef X mul
-- statement:
--   The coefficients of t_l·f.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L133-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L133-L136

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

theorem ClauseBound.Boson.Text.coef_X_mul (π : Multiset ℕ) (l : ℕ) (f : Rg) : coef π (X l * f) = if l ∈ π then coef (π.erase l) f else 0 := by sorry
