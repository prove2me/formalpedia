-- Prove2me | Theorems.Thm_ClauseBound_Boson_Text_nabPos_mon
-- name    : ClauseBound.Boson.Text.nabPos_mon
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:19:37.24255+00:00
-- url     : https://prove2.me/theorems/ac73b4c4-9986-4066-923b-a7527446f748
-- title:
--   Text: nab Pos mon
-- statement:
--   ∇ₖ on a monomial.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L139-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L139-L142

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

theorem ClauseBound.Boson.Text.nabPos_mon (k : ℕ) (σ : Multiset ℕ) : nabPos (k : ℤ) (mon σ) = ((k : ℤ) * σ.count k) • mon (σ.erase k) := by sorry
