-- Prove2me | Theorems.Thm_ClauseBound_Gen_Pick_lt_K_succ
-- name    : ClauseBound.Gen.Pick.lt_K_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:12:04.420339+00:00
-- url     : https://prove2.me/theorems/fd9aedc7-594d-41c8-b6ec-3a717179a93d
-- title:
--   Pick: lt K succ
-- statement:
--   ℓ < K_{ℓ+1}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L56-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L56-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Gen_Pick
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Pick
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen

theorem ClauseBound.Gen.Pick.lt_K_succ (x₀ l : ℕ) : l < K x₀ (l + 1) := by sorry
