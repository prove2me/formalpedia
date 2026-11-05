-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_hF_eq
-- name    : ClauseBound.Inst.Half.hF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:51:16.779202+00:00
-- url     : https://prove2.me/theorems/8cc241ed-fc89-48c6-8ef1-b94b765808b3
-- title:
--   Half: h F eq
-- statement:
--   `hF` finds `hOf lam` if that number is at most c₀·lam².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L141-L151
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L141-L151

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

theorem ClauseBound.Inst.Half.hF_eq {c₀ lam : ℕ} (h : hOf lam ≤ c₀ * lam ^ 2) : hF c₀ lam = hOf lam := by sorry
