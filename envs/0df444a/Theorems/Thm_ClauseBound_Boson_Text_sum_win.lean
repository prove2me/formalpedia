-- Prove2me | Theorems.Thm_ClauseBound_Boson_Text_sum_win
-- name    : ClauseBound.Boson.Text.sum_win
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:00:07.307234+00:00
-- url     : https://prove2.me/theorems/db602838-1a8a-481a-9efa-d855d8c3df2f
-- title:
--   Text: sum win
-- statement:
--   A sum over the window.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L104-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L104-L115

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

theorem ClauseBound.Boson.Text.sum_win (M : ℕ) (G : ℤ → ℤ) : ∑ k ∈ win M, G k = ∑ l ∈ Icc 1 M, G (-(l : ℤ)) + ∑ k ∈ Icc 1 M, G (k : ℤ) := by sorry
