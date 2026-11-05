-- Prove2me | Theorems.Thm_ClauseBound_Boson_Text_sum_tup_succ
-- name    : ClauseBound.Boson.Text.sum_tup_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:01:08.68628+00:00
-- url     : https://prove2.me/theorems/62ad8d2c-aa42-4438-b968-bd1b727696d3
-- title:
--   Text: sum tup succ
-- statement:
--   A sum over the tuples of length q + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L118-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L118-L122

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

theorem ClauseBound.Boson.Text.sum_tup_succ (M q : ℕ) (G : List ℤ → ℤ) : ∑ ks ∈ tup M (q + 1), G ks = ∑ k ∈ win M, ∑ ks ∈ tup M q, G (k :: ks) := by sorry
