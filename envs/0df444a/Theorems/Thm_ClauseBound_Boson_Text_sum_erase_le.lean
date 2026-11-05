-- Prove2me | Theorems.Thm_ClauseBound_Boson_Text_sum_erase_le
-- name    : ClauseBound.Boson.Text.sum_erase_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:01:19.667218+00:00
-- url     : https://prove2.me/theorems/5563d6d1-01fb-4c57-98e3-bdbb4bbc5e66
-- title:
--   Text: sum erase le
-- statement:
--   The Text construction uses the sum erase le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L178-L182
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L178-L182

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

theorem ClauseBound.Boson.Text.sum_erase_le (π : Multiset ℕ) (l : ℕ) : (π.erase l).sum ≤ π.sum := by sorry
