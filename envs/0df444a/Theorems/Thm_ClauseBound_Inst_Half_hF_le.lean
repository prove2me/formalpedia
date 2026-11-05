-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_hF_le
-- name    : ClauseBound.Inst.Half.hF_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:17:04.518339+00:00
-- url     : https://prove2.me/theorems/bfedb6dd-a692-44ef-843b-ecf820e95815
-- title:
--   Half: h F le
-- statement:
--   `hF` is at most c₀·lam² + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L154-L160
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L154-L160

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset

theorem ClauseBound.Inst.Half.hF_le (c₀ lam : ℕ) : hF c₀ lam ≤ c₀ * lam ^ 2 + 2 := by sorry
