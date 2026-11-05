-- Prove2me | Theorems.Thm_ClauseBound_Boson_Size_sum_erase_le
-- name    : ClauseBound.Boson.Size.sum_erase_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:38:05.463211+00:00
-- url     : https://prove2.me/theorems/fe2639f2-a944-4f1b-993e-a7cdd1c014e4
-- title:
--   Size: sum erase le
-- statement:
--   Taking a part away does not raise the weight.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Size.lean#L44-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Size.lean#L44-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Rec_Window
import Definitions.Def_ClauseBound_Boson_Size
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Size

theorem ClauseBound.Boson.Size.sum_erase_le (π : Multiset ℕ) (l : ℕ) : (π.erase l).sum ≤ π.sum := by sorry
