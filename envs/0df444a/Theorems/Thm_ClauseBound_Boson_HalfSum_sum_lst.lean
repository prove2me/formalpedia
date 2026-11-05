-- Prove2me | Theorems.Thm_ClauseBound_Boson_HalfSum_sum_lst
-- name    : ClauseBound.Boson.HalfSum.sum_lst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:18:45.065995+00:00
-- url     : https://prove2.me/theorems/1c84e137-e984-406d-9d7b-ab306d8595de
-- title:
--   Half Sum: sum lst
-- statement:
--   The parts add up to h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/HalfSum.lean#L30-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/HalfSum.lean#L30-L31

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_HalfSum
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson ClauseBound.Boson.HalfSum
open Finset

theorem ClauseBound.Boson.HalfSum.sum_lst {h : ℕ} (q : Nat.Partition h) : (lst q).sum = h := by sorry
